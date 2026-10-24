// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The sans-I/O core of a session; see [`SessionCore`].

// Without the feature, only what `Session` uses is reachable.
#![cfg_attr(not(feature = "unstable-sans-io"), allow(dead_code))]

use std::collections::VecDeque;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::time::{Duration, Instant};

use bytes::Bytes;
use log::{debug, trace, warn};
use url::Url;

use super::channel_mapping::ChannelType;
use super::conn::{ConnCore, ResponseMode};
use super::parse::{self, SessionHeader};
use super::playing::{PlayingCore, PlayingStream};
use super::teardown::TeardownCore;
use super::{
    InitialSequenceNumberPolicy, InitialTimestampPolicy, PlayOptions, Presentation, SessionFlag,
    SessionIdPolicy, SessionOptions, Stream, StreamDirection, StreamState, StreamStateInit,
    TeardownPolicy, Tool, UnknownRtcpSsrcPolicy, receiver_report, rtp,
};
use crate::buf::MarkBuf;
use crate::rtsp::msg::{self, OwnedMessage};
use crate::{
    ConnectionContext, Error, ErrorInt, StreamContext, StreamContextInner, TcpStreamContext,
    UdpStreamContext, WallTime,
};

/// The transport to request in [`SessionCore::setup`].
#[derive(Copy, Clone, Debug)]
#[non_exhaustive]
pub enum SetupTransport {
    /// RTP/AVP/TCP: interleave RTP and RTCP on the RTSP connection.
    Tcp,

    /// RTP/AVP/UDP: send RTP and RTCP to a pair of UDP sockets the caller has
    /// bound on the RTSP connection's local address, on ports `client_rtp_port`
    /// (even) and `client_rtp_port + 1`. See [`crate::UdpPair`].
    Udp { client_rtp_port: u16 },
}

/// A packet to send on a UDP stream's socket, from
/// [`SessionCore::poll_transmit_udp`].
#[derive(Debug)]
#[non_exhaustive]
pub struct UdpTransmit {
    /// The index of the stream within [`SessionCore::streams`].
    pub stream_i: usize,

    /// Which of the stream's sockets to send on.
    pub channel_type: ChannelType,

    pub data: Vec<u8>,
}

/// A completed request, from [`SessionCore::poll_event`].
#[derive(Debug)]
#[non_exhaustive]
pub enum SessionEvent {
    /// [`SessionCore::describe`] succeeded; [`SessionCore::streams`] is now
    /// populated.
    Described,

    /// [`SessionCore::setup`] succeeded on stream `stream_i`.
    SetUp {
        stream_i: usize,

        /// For a UDP stream, the server's RTP address; RTCP is on the next
        /// port. Connect the stream's sockets to these addresses, then send
        /// the packets from [`SessionCore::poll_transmit_udp`].
        udp_peer: Option<SocketAddr>,
    },

    /// [`SessionCore::play`] succeeded. From now on, packets come from
    /// [`SessionCore::poll_item`].
    Playing,

    /// [`SessionCore::teardown`] succeeded, or the server says the session no
    /// longer exists.
    TornDown,
}

/// The request [`SessionCore`] is waiting on.
enum Op {
    Describe {
        url: Url,
    },
    Setup {
        stream_i: usize,
        udp: Option<UdpStreamContext>,
    },
    Play {
        options: PlayOptions,
    },
    Teardown,
}

/// The state of a session before it's playing; see [`SessionCore`].
pub(crate) struct SetupCore {
    conn: ConnCore,
    presentation: Option<Presentation>,
    sdp: Bytes,

    /// Set iff one or more `SETUP` requests have succeeded.
    session: Option<SessionHeader>,

    op: Option<Op>,

    /// Bitmask of [`SessionFlag`]s.
    flags: u8,

    transmit_udp: VecDeque<UdpTransmit>,

    /// Set once the `PLAY` response has been handled, for
    /// [`SetupCore::into_playing`].
    played: Option<Box<[Option<PlayingStream>]>>,
}

impl SetupCore {
    /// Creates a core for a newly established RTSP connection from
    /// `local_addr` to `peer_addr`.
    pub(crate) fn new(
        local_addr: SocketAddr,
        peer_addr: SocketAddr,
        options: SessionOptions,
    ) -> Self {
        let ctx = ConnectionContext {
            local_addr,
            peer_addr,
            established_wall: WallTime::now(),
        };
        Self::from_conn(ConnCore::new(ctx, options))
    }

    pub(crate) fn from_conn(conn: ConnCore) -> Self {
        Self {
            conn,
            presentation: None,
            sdp: Bytes::new(),
            session: None,
            op: None,
            flags: 0,
            transmit_udp: VecDeque::new(),
            played: None,
        }
    }

    /// Creates a core for a session which was playing, so that it can be torn
    /// down; see [`PlayingCore::into_setup`].
    pub(crate) fn from_playing(
        conn: ConnCore,
        presentation: Presentation,
        sdp: Bytes,
        session: SessionHeader,
        flags: u8,
    ) -> Self {
        Self {
            presentation: Some(presentation),
            sdp,
            session: Some(session),
            flags,
            ..Self::from_conn(conn)
        }
    }

    /// Returns a context for the RTSP connection, e.g. for error messages.
    #[inline]
    pub(crate) fn conn_ctx(&self) -> &ConnectionContext {
        &self.conn.ctx
    }

    /// Returns the buffer the caller should fill with bytes received on the
    /// RTSP connection, via `spare_capacity` and `advance_end`.
    #[inline]
    pub(crate) fn read_buf(&mut self) -> &mut MarkBuf {
        self.conn.read_buf()
    }

    /// Notes that the peer has closed the RTSP connection.
    ///
    /// A request awaiting its response then fails.
    pub(crate) fn handle_eof(&mut self) {
        self.conn.eof = true;
    }

    pub(crate) fn is_closed(&self) -> bool {
        self.conn.eof
    }

    /// Returns an error for a failed read from the RTSP connection.
    pub(crate) fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.conn.read_error(source, now)
    }

    /// Returns the streams in the presentation; empty until
    /// [`SessionEvent::Described`].
    pub(crate) fn streams(&self) -> &[Stream] {
        self.presentation
            .as_ref()
            .map(|p| &p.streams[..])
            .unwrap_or_default()
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's
    /// `a:tool` SDP attribute.
    pub(crate) fn tool(&self) -> Option<&Tool> {
        self.conn.tool.as_ref()
    }

    /// Returns the raw SDP from the `DESCRIBE` response; empty until
    /// [`SessionEvent::Described`].
    pub(crate) fn sdp(&self) -> &[u8] {
        &self.sdp
    }

    /// Returns the bytes to write to the RTSP connection, in order.
    pub(crate) fn transmit_buf(&self) -> (&[u8], &[u8]) {
        self.conn.transmit_buf()
    }

    /// Notes that the first `n` bytes of [`SetupCore::transmit_buf`] have
    /// been written.
    pub(crate) fn advance_transmit(&mut self, n: usize) {
        self.conn.advance_transmit(n);
    }

    /// Returns a packet to send on a UDP stream's socket, if any.
    pub(crate) fn poll_transmit_udp(&mut self) -> Option<UdpTransmit> {
        self.transmit_udp.pop_front()
    }

    fn start(&mut self, mode: ResponseMode, op: Op, req: OwnedMessage) -> Result<(), Error> {
        if self.op.is_some() || self.conn.has_pending() {
            bail!(ErrorInt::FailedPrecondition(
                "another request is in progress".into()
            ));
        }
        self.conn.send(mode, req)?;
        self.op = Some(op);
        Ok(())
    }

    /// Starts a `DESCRIBE` request for `url`.
    ///
    /// `url` must use the `rtsp` scheme and must not contain credentials;
    /// supply those via [`SessionOptions::creds`].
    pub(crate) fn describe(&mut self, url: Url) -> Result<(), Error> {
        if self.presentation.is_some() {
            bail!(ErrorInt::FailedPrecondition("already described".into()));
        }
        super::validate_url(&url).map_err(|e| wrap!(ErrorInt::InvalidArgument(e)))?;
        let mut headers: msg::Headers = [(
            msg::HeaderName::ACCEPT,
            msg::HeaderValue::try_from("application/sdp").unwrap(),
        )]
        .into();
        if self.conn.options.backchannel {
            // ONVIF Streaming Specification section 5.3.2: "A client shall
            // include the feature tag in its DESCRIBE request to indicate that a
            // bidirectional data connection shall be established."
            headers.insert(msg::HeaderName::REQUIRE, super::backchannel_require());
        }
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::DESCRIBE,
                request_uri: Some(url.clone()),
                headers,
            },
            body: Bytes::new(),
        };
        self.start(ResponseMode::Normal, Op::Describe { url }, req)
    }

    /// Starts a `SETUP` request for stream `stream_i`.
    ///
    /// These can't reasonably be pipelined because subsequent requests are
    /// expected to adopt the previous response's `Session`. Likewise, the
    /// server may override the preferred interleaved channel id and it seems
    /// like a bad idea to try to assign more interleaved channels without
    /// inspecting that first.
    ///
    /// A [`super::StreamDirection::Sending`] stream (ONVIF backchannel) can
    /// currently only be set up with [`SetupTransport::Tcp`]; `SETUP` with
    /// [`SetupTransport::Udp`] fails without sending a request.
    ///
    /// Panics if `stream_i >= self.streams().len()`.
    pub(crate) fn setup(
        &mut self,
        stream_i: usize,
        transport: SetupTransport,
    ) -> Result<(), Error> {
        let Some(presentation) = self.presentation.as_ref() else {
            bail!(ErrorInt::FailedPrecondition(
                "must DESCRIBE before SETUP".into()
            ));
        };
        let stream = &presentation.streams[stream_i];
        if !matches!(stream.state, StreamState::Uninit) {
            bail!(ErrorInt::FailedPrecondition("stream already set up".into()));
        }
        let sending = stream.direction == StreamDirection::Sending;
        if sending && matches!(transport, SetupTransport::Udp { .. }) {
            bail!(ErrorInt::Unsupported(format!(
                "stream {stream_i} is an ONVIF backchannel (a=sendonly), which Retina can only send \
                 over TCP"
            )));
        }
        let url = stream
            .control
            .as_ref()
            .unwrap_or(&presentation.control)
            .clone();
        let mut headers = msg::Headers::default();
        if sending {
            // ONVIF Streaming Specification section 5.3.1: the `Require`
            // header "shall be included in any request where the server is
            // required to understand that feature to correctly perform the
            // request". Section 5.3.2.2's example sends it on the
            // backchannel's `SETUP` and not on the others.
            headers.insert(msg::HeaderName::REQUIRE, super::backchannel_require());
        }
        let udp = match transport {
            SetupTransport::Tcp => {
                let proposed_channel_id =
                    self.conn.channels.next_unassigned().ok_or_else(|| {
                        wrap!(ErrorInt::FailedPrecondition(
                            "no unassigned channels".into()
                        ))
                    })?;
                headers.insert(
                    msg::HeaderName::TRANSPORT,
                    msg::HeaderValue::try_from(format!(
                        "RTP/AVP/TCP;unicast;interleaved={}-{}",
                        proposed_channel_id,
                        proposed_channel_id + 1
                    ))
                    .unwrap(),
                );
                None
            }
            SetupTransport::Udp { client_rtp_port } => {
                headers.insert(
                    msg::HeaderName::TRANSPORT,
                    msg::HeaderValue::try_from(format!(
                        "RTP/AVP/UDP;unicast;client_port={}-{}",
                        client_rtp_port,
                        client_rtp_port + 1,
                    ))
                    .unwrap(),
                );
                Some(UdpStreamContext {
                    local_ip: self.conn.ctx.local_addr.ip(),
                    peer_ip: IpAddr::V4(Ipv4Addr::UNSPECIFIED),
                    local_rtp_port: client_rtp_port,
                    peer_rtp_port: 0,
                })
            }
        };
        if let Some(s) = &self.session {
            headers.insert(msg::HeaderName::SESSION, s.id.clone());
        }
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::SETUP,
                request_uri: Some(url),
                headers,
            },
            body: Bytes::new(),
        };
        self.start(ResponseMode::Normal, Op::Setup { stream_i, udp }, req)?;
        self.flags |= if udp.is_some() {
            SessionFlag::UdpStreams
        } else {
            SessionFlag::TcpStreams
        } as u8;
        Ok(())
    }

    /// Starts a `PLAY` request for the entire presentation.
    ///
    /// The presentation must support aggregate control, as defined in [RFC 2326
    /// section 1.3](https://tools.ietf.org/html/rfc2326#section-1.3).
    ///
    /// If a [`super::StreamDirection::Sending`] stream has been set up, the
    /// request carries the ONVIF backchannel `Require` header.
    pub(crate) fn play(&mut self, options: PlayOptions) -> Result<(), Error> {
        let (Some(presentation), Some(session)) = (&self.presentation, &self.session) else {
            bail!(ErrorInt::FailedPrecondition(
                "must SETUP before PLAY".into()
            ));
        };
        if self.played.is_some() {
            bail!(ErrorInt::FailedPrecondition("already playing".into()));
        }
        if let Some(t) = &self.conn.tool
            && (self.flags & (SessionFlag::TcpStreams as u8)) != 0
            && t.has_live555_tcp_bug()
        {
            warn!(
                "Connecting via TCP to known-broken RTSP server {:?}. \
                 See <https://github.com/scottlamb/retina/issues/17>. \
                 Consider using UDP instead!",
                t
            );
        }
        trace!("PLAY with channel mappings: {:#?}", self.conn.channels);
        let mut headers: msg::Headers = [
            (msg::HeaderName::SESSION, session.id.clone()),
            (
                msg::HeaderName::RANGE,
                msg::HeaderValue::try_from("npt=0.000-").unwrap(),
            ),
        ]
        .into();
        if self.flags & (SessionFlag::Backchannel as u8) != 0 {
            // ONVIF Streaming Specification section 5.3.2.2: "The
            // Require-header indicates that a special interpretation of the
            // PLAY command is necessary. The command covers both starting of
            // the video and audio stream from NVT to the client and starting
            // the audio connection from client to server."
            headers.insert(msg::HeaderName::REQUIRE, super::backchannel_require());
        }
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::PLAY,
                request_uri: Some(presentation.control.clone()),
                headers,
            },
            body: Bytes::new(),
        };
        self.start(ResponseMode::Play, Op::Play { options }, req)?;
        self.flags |= SessionFlag::MaybePlaying as u8;
        Ok(())
    }

    /// Starts a `TEARDOWN` request for the session.
    ///
    /// This can follow a failed request, but not one still in progress.
    /// Interleaved data and unrelated responses are ignored until the
    /// `TEARDOWN` response arrives.
    pub(crate) fn teardown(&mut self) -> Result<(), Error> {
        let req = self.teardown_request()?;
        self.start(ResponseMode::Teardown, Op::Teardown, req)
    }

    /// Switches to a [`TeardownCore`], per the [`TeardownPolicy`], or returns
    /// `None` if there's nothing to do.
    ///
    /// Tracks the session in its [`super::SessionGroup`], if any.
    pub(crate) fn into_teardown(self, now: Instant) -> Option<TeardownCore> {
        let has_tcp = (self.flags & (SessionFlag::TcpStreams as u8)) != 0;
        let just_try_once = match self.conn.options.teardown {
            TeardownPolicy::Auto if has_tcp => {
                // If the server is known to have the live555 bug, try really
                // hard to send a TEARDOWN before considering the session
                // cleaned up. Otherwise, try once on the existing connection,
                // primarily in case the server has this bug but doesn't
                // advertise a buggy version.
                !self.tool().is_some_and(Tool::has_live555_tcp_bug)
            }
            TeardownPolicy::Auto | TeardownPolicy::Always => false,
            TeardownPolicy::Never => return None,
        };
        let req = self.teardown_request().ok()?;
        let session = self.session.as_ref().expect("teardown_request checked");
        let base_url = self
            .presentation
            .as_ref()
            .expect("teardown_request checked")
            .base_url
            .clone();

        // For now, assume the whole timeout is left.
        let expires = now + Duration::from_secs(session.timeout_sec.into());
        let tracked = self.conn.options.session_group.clone().map(|group| {
            let seqnum = group.add(
                now,
                super::StaleTeardown::Pending,
                (self.flags & (SessionFlag::MaybePlaying as u8)) != 0,
                has_tcp,
                expires,
            );
            debug!(
                "{:?}/{} tracking TEARDOWN of session id {}",
                group.debug_id(),
                seqnum,
                &*session.id
            );
            (group, seqnum)
        });
        let session_id = session.id.clone();
        Some(TeardownCore::new(
            self.conn,
            req,
            session_id,
            base_url,
            just_try_once,
            expires,
            tracked,
            now,
        ))
    }

    /// Returns a `TEARDOWN` request for the session, minus the headers
    /// [`ConnCore::send`] adds.
    fn teardown_request(&self) -> Result<OwnedMessage, Error> {
        let (Some(presentation), Some(session)) = (&self.presentation, &self.session) else {
            bail!(ErrorInt::FailedPrecondition(
                "no session to tear down".into()
            ));
        };
        let mut headers: msg::Headers = [(msg::HeaderName::SESSION, session.id.clone())].into();
        if self.flags & (SessionFlag::Backchannel as u8) != 0 {
            // ONVIF Streaming Specification section 5.3.1: "An RTSP client that
            // wants to build up an RTSP connection with a data backchannel shall
            // include the Require header in its requests." Section 5.3.2.2's
            // example `TEARDOWN` carries it too.
            headers.insert(msg::HeaderName::REQUIRE, super::backchannel_require());
        }
        Ok(OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::TEARDOWN,
                request_uri: Some(presentation.base_url.clone()),
                headers,
            },
            body: Bytes::new(),
        })
    }

    /// Processes received data, returning the request which completed, if any.
    ///
    /// On error, the session should be abandoned (possibly after trying
    /// [`SessionCore::teardown`]).
    pub(crate) fn poll_event(&mut self, now: Instant) -> Option<Result<SessionEvent, Error>> {
        self.op.as_ref()?;
        let r = self.conn.poll_response(now)?;
        let op = self.op.take().expect("op is set");
        Some(match (op, r) {
            (Op::Teardown, r) => super::teardown::status(r).map(|_| SessionEvent::TornDown),
            (Op::Describe { .. }, Err(e)) if self.conn.options.backchannel => {
                Err(note_backchannel_unsupported(e))
            }
            (_, Err(e)) => Err(e),
            (Op::Describe { url }, Ok(r)) => self.handle_describe(url, r),
            (Op::Setup { stream_i, udp }, Ok(r)) => self.handle_setup(stream_i, udp, r),
            (Op::Play { options }, Ok(r)) => self.handle_play(options, r),
        })
    }

    fn handle_describe(
        &mut self,
        url: Url,
        r: super::conn::Response,
    ) -> Result<SessionEvent, Error> {
        let presentation =
            parse::parse_describe(url, &r.head, &r.body, self.conn.options.backchannel)
                .map_err(|description| r.error(&self.conn.ctx, description))?;
        self.conn.tool = presentation.tool.clone();
        self.presentation = Some(presentation);
        self.sdp = r.body;
        Ok(SessionEvent::Described)
    }

    fn handle_setup(
        &mut self,
        stream_i: usize,
        udp: Option<UdpStreamContext>,
        r: super::conn::Response,
    ) -> Result<SessionEvent, Error> {
        debug!("SETUP response: {:#?}", r.head);
        let conn_ctx = self.conn.ctx;
        let response =
            parse::parse_setup(&r.head).map_err(|description| r.error(&conn_ctx, description))?;
        match &self.session {
            Some(SessionHeader { id, .. }) if *id != response.session.id => {
                if !matches!(self.conn.options.session_id, SessionIdPolicy::UseFirst) {
                    return Err(r.error(
                        &conn_ctx,
                        format!(
                            "session id changed from {:?} to {:?}",
                            id, response.session.id,
                        ),
                    ));
                }
            }
            Some(_) => {}
            None => {
                debug!(
                    "established session {:?}, timeout={}s",
                    response.session.id, response.session.timeout_sec
                );
                self.session = Some(response.session);
            }
        };
        let (ctx, udp_peer) = match udp {
            None => {
                let Some(channel_id) = response.channel_id else {
                    return Err(r.error(
                        &conn_ctx,
                        "Transport header is missing interleaved parameter".to_owned(),
                    ));
                };
                self.conn
                    .channels
                    .assign(channel_id, stream_i)
                    .map_err(|description| r.error(&conn_ctx, description))?;
                (
                    StreamContext(StreamContextInner::Tcp(TcpStreamContext {
                        rtp_channel_id: channel_id,
                    })),
                    None,
                )
            }
            Some(mut ctx) => {
                // TODO: RFC 2326 section 12.39 says "If the source address for
                // the stream is different than can be derived from the RTSP
                // endpoint address (the server in playback or the client in
                // recording), the source MAY be specified." Not MUST,
                // unfortunately. But let's see if we can get away with this
                // for now.
                let source = response.source.unwrap_or(conn_ctx.peer_addr.ip());
                let Some(server_port) = response.server_port else {
                    return Err(r.error(
                        &conn_ctx,
                        "Transport header is missing server_port parameter".to_owned(),
                    ));
                };
                ctx.peer_ip = source;
                ctx.peer_rtp_port = server_port;
                for (channel_type, data) in [
                    (ChannelType::Rtp, &HOLE_PUNCH_RTP[..]),
                    (ChannelType::Rtcp, &HOLE_PUNCH_RTCP[..]),
                ] {
                    self.transmit_udp.push_back(UdpTransmit {
                        stream_i,
                        channel_type,
                        data: data.to_vec(),
                    });
                }
                (
                    StreamContext(StreamContextInner::Udp(ctx)),
                    Some(SocketAddr::new(source, server_port)),
                )
            }
        };
        let stream = &mut self.presentation.as_mut().expect("described").streams[stream_i];
        if stream.direction == StreamDirection::Sending {
            self.flags |= SessionFlag::Backchannel as u8;
        }
        stream.state = StreamState::Init(StreamStateInit {
            ssrc: response.ssrc,
            initial_seq: None,
            initial_rtptime: None,
            ctx,
        });
        Ok(SessionEvent::SetUp { stream_i, udp_peer })
    }

    fn handle_play(
        &mut self,
        policy: PlayOptions,
        r: super::conn::Response,
    ) -> Result<SessionEvent, Error> {
        let conn_ctx = self.conn.ctx;
        let presentation = self.presentation.as_mut().expect("described");
        parse::parse_play(&r.head, presentation)
            .map_err(|description| r.error(&conn_ctx, description))?;

        // Count how many streams to receive have been setup (not how many are
        // in the presentation). Sending streams have no say in timestamps:
        // servers don't necessarily describe them in `RTP-Info`.
        let setup_streams = presentation
            .streams
            .iter()
            .filter(|s| {
                s.direction == StreamDirection::Receiving && matches!(s.state, StreamState::Init(_))
            })
            .count();

        let all_have_time = presentation.streams.iter().all(|s| match s.state {
            StreamState::Init(StreamStateInit {
                initial_rtptime, ..
            }) if s.direction == StreamDirection::Receiving => initial_rtptime.is_some(),
            _ => true,
        });

        // Check that required parameters are present on all streams that have
        // been set up, before changing any state.
        let mut core_streams: Box<[Option<PlayingStream>]> =
            presentation.streams.iter().map(|_| None).collect();
        for (i, s) in presentation.streams.iter().enumerate() {
            let StreamState::Init(StreamStateInit {
                initial_rtptime,
                initial_seq,
                ssrc,
                ctx,
            }) = s.state
            else {
                continue;
            };
            if s.direction == StreamDirection::Sending {
                // The receiver handles RTCP receiver reports the server sends
                // about Retina's packets. These have the server's SSRC, so
                // don't expect Retina's. Its timeline only places timestamps
                // of any RTCP sender reports the server sends on this stream.
                let receiver = crate::rtp::Receiver::new(
                    s.clock_rate_hz,
                    crate::rtp::ReceiverOptions::default(),
                )
                .map_err(|e| r.error(&conn_ctx, e.to_string()))?;
                core_streams[i] = Some(PlayingStream {
                    rtp_handler: rtp::StreamReceiver::new(receiver, policy.unknown_rtcp_ssrc),
                    ctx,
                    udp_buf: None,

                    // Receiver reports describe only media Retina receives.
                    reception: None,
                    sending: true,
                });
                continue;
            }
            let initial_rtptime = match policy.initial_timestamp {
                InitialTimestampPolicy::Require | InitialTimestampPolicy::Default
                    if setup_streams > 1 =>
                {
                    if initial_rtptime.is_none() {
                        return Err(r.error(
                            &conn_ctx,
                            format!(
                                "Expected rtptime on PLAY with mode {:?}, missing on \
                                 stream {} ({:?}). Consider setting initial timestamp \
                                 mode permissive.",
                                policy.initial_timestamp, i, s.control
                            ),
                        ));
                    }
                    initial_rtptime
                }
                InitialTimestampPolicy::Permissive if setup_streams > 1 && all_have_time => {
                    initial_rtptime
                }
                _ => None,
            };
            let initial_seq = match (initial_seq, policy.initial_seq) {
                (Some(seq), InitialSequenceNumberPolicy::Ignore)
                | (
                    Some(seq @ 0 | seq @ 1),
                    InitialSequenceNumberPolicy::Default
                    | InitialSequenceNumberPolicy::IgnoreSuspiciousValues,
                ) => {
                    log::info!(
                        "ignoring PLAY seq={} on stream {} due to policy {:?}",
                        seq,
                        i,
                        policy.initial_seq
                    );
                    None
                }
                (Some(seq), _) => {
                    log::debug!("setting PLAY seq={} on stream {}", seq, i);
                    Some(seq)
                }
                (None, _) => {
                    log::debug!("no PLAY seq on stream {}", i);
                    None
                }
            };
            let mut options = crate::rtp::ReceiverOptions::default()
                .max_forward_jump_secs(policy.enforce_timestamps_with_max_jump_secs)
                .out_of_order(if matches!(ctx.0, StreamContextInner::Udp(_)) {
                    crate::rtp::OutOfOrder::Drop
                } else {
                    crate::rtp::OutOfOrder::Error
                })
                .learn_ssrc_from_sender_report(!matches!(
                    policy.unknown_rtcp_ssrc,
                    UnknownRtcpSsrcPolicy::ProcessPackets
                ));
            if let Some(ssrc) = ssrc {
                options = options.ssrc(ssrc);
            }
            if let Some(seq) = initial_seq {
                options = options.initial_sequence_number(seq);
            }
            if let Some(rtptime) = initial_rtptime {
                options = options.initial_rtptime(rtptime);
            }
            let receiver = crate::rtp::Receiver::new(s.clock_rate_hz, options)
                .map_err(|e| r.error(&conn_ctx, e.to_string()))?;
            core_streams[i] = Some(PlayingStream {
                rtp_handler: rtp::StreamReceiver::new(receiver, policy.unknown_rtcp_ssrc),
                ctx,
                udp_buf: matches!(ctx.0, StreamContextInner::Udp(_)).then(|| MarkBuf::new(65536)),
                reception: self
                    .conn
                    .options
                    .receiver_reports
                    .enabled()
                    .then(|| receiver_report::ReceptionStats::new(s.clock_rate_hz)),
                sending: false,
            });
        }

        // Move all streams that have been set up from Init to Playing state.
        for s in presentation.streams.iter_mut() {
            if let StreamState::Init(StreamStateInit { ctx, .. }) = s.state {
                s.state = StreamState::Playing { ctx };
            }
        }
        self.played = Some(core_streams);
        Ok(SessionEvent::Playing)
    }

    /// Switches to a [`PlayingCore`], after [`SessionEvent::Playing`].
    ///
    /// Data already received after the `PLAY` response stays buffered for the
    /// new core.
    ///
    /// Panics if `PLAY` hasn't succeeded.
    pub(crate) fn into_playing(self, now: Instant) -> PlayingCore {
        let streams = self
            .played
            .expect("into_playing requires a successful PLAY");
        PlayingCore::new(
            self.conn,
            self.presentation.expect("played implies described"),
            self.sdp,
            self.session.expect("played implies set up"),
            streams,
            self.flags,
            now,
        )
    }
}

/// Points out the likely cause of a failed `DESCRIBE` with the backchannel
/// requested.
///
/// ONVIF Streaming Specification section 5.3.2: "An RTSP server that does not
/// understand the backchannel feature tag or does not support bidirectional
/// data connections shall respond with an error code 551 Option not
/// supported".
fn note_backchannel_unsupported(e: Error) -> Error {
    match &*e.0 {
        ErrorInt::RtspResponseError {
            conn_ctx,
            msg_ctx,
            method,
            cseq,
            status,
            description,
        } if *status == msg::StatusCode::OPTION_NOT_SUPPORTED => {
            wrap!(ErrorInt::RtspResponseError {
                conn_ctx: *conn_ctx,
                msg_ctx: *msg_ctx,
                method: method.clone(),
                cseq: *cseq,
                status: *status,
                description: format!(
                    "{description}; the server may not support the ONVIF backchannel \
                     requested via SessionOptions::backchannel"
                ),
            })
        }
        _ => e,
    }
}

/// The sans-I/O state of an RTSP client session.
///
/// This is the protocol logic of [`super::Session`] without sockets or
/// timers, for callers who do their own I/O. One core covers the session's
/// whole life; methods which don't apply in its current phase return an error
/// (or nothing to do) at runtime.
///
/// The caller connects to the server and creates a core via
/// [`SessionCore::new`]. Throughout, it:
///
/// *   writes the bytes from [`SessionCore::transmit_buf`] to the RTSP
///     connection, followed by [`SessionCore::advance_transmit`].
/// *   reads from the RTSP connection into [`SessionCore::read_buf`], via
///     [`MarkBuf::spare_capacity`] and [`MarkBuf::advance_end`], calling
///     [`SessionCore::handle_eof`] if the server closes the connection.
/// *   sends the packets from [`SessionCore::poll_transmit_udp`] on UDP
///     streams' sockets.
///
/// To start the session, it calls [`SessionCore::describe`],
/// [`SessionCore::setup`] (for each desired stream), and
/// [`SessionCore::play`] in turn, doing I/O until [`SessionCore::poll_event`]
/// returns each completed request. Only one request may be outstanding at a
/// time. After a UDP stream's [`SessionEvent::SetUp`], it connects that
/// stream's sockets before sending the packets from
/// [`SessionCore::poll_transmit_udp`]. The core has no timers before `PLAY`;
/// the caller should give up on a request that takes too long.
///
/// Once [`SessionEvent::Playing`] is returned, the caller additionally:
///
/// *   reads from each UDP stream's sockets into [`SessionCore::udp_buf`],
///     followed by [`SessionCore::udp_received`].
/// *   gets packets via [`SessionCore::poll_item`].
/// *   sends media on any ONVIF backchannel streams via [`SessionCore::queue_rtp`].
/// *   calls [`SessionCore::handle_timeout`] at [`SessionCore::poll_timeout`],
///     for keepalives and RTCP receiver reports. Keepalives keep the session
///     alive only as long as the caller does all this, so it shouldn't stall
///     on handling items.
///
/// [`SessionCore::teardown`] ends the session, before or after `PLAY`.
pub struct SessionCore(Phase);

enum Phase {
    Setup(SetupCore),
    Playing(PlayingCore),

    /// Only briefly, while switching phases.
    Switching,
}

impl SessionCore {
    /// Creates a core for a newly established RTSP connection from
    /// `local_addr` to `peer_addr`.
    pub fn new(local_addr: SocketAddr, peer_addr: SocketAddr, options: SessionOptions) -> Self {
        Self(Phase::Setup(SetupCore::new(local_addr, peer_addr, options)))
    }

    #[cfg(feature = "tokio")]
    pub(crate) fn from_conn(conn: ConnCore) -> Self {
        Self(Phase::Setup(SetupCore::from_conn(conn)))
    }

    fn setup_core(&mut self) -> Result<&mut SetupCore, Error> {
        match &mut self.0 {
            Phase::Setup(c) => Ok(c),
            _ => bail!(ErrorInt::FailedPrecondition("already playing".into())),
        }
    }

    /// Returns the playing state, iff [`SessionEvent::Playing`] has been
    /// returned (and the session hasn't since been torn down).
    pub(crate) fn playing_mut(&mut self) -> Option<&mut PlayingCore> {
        match &mut self.0 {
            Phase::Playing(c) => Some(c),
            _ => None,
        }
    }

    pub(crate) fn playing(&self) -> Option<&PlayingCore> {
        match &self.0 {
            Phase::Playing(c) => Some(c),
            _ => None,
        }
    }

    /// Takes the state needed for a `TEARDOWN`, leaving this core unusable.
    #[cfg(feature = "tokio")]
    pub(crate) fn take_setup(&mut self) -> Option<SetupCore> {
        match std::mem::replace(&mut self.0, Phase::Switching) {
            Phase::Setup(c) => Some(c),
            Phase::Playing(c) => Some(c.into_setup()),
            Phase::Switching => None,
        }
    }

    /// Consumes the session, returning a [`TeardownCore`] to end it on the
    /// server per [`SessionOptions::teardown`], or `None` if there's nothing to
    /// do: the policy is [`super::TeardownPolicy::Never`], or no `SETUP` has
    /// succeeded.
    ///
    /// This is what a dropped [`super::Session`] does in the background. It
    /// can follow a failed request, or interrupt one in progress. If the
    /// session has a [`super::SessionGroup`], it's tracked there until the
    /// `TeardownCore` finishes.
    pub fn into_teardown(self, now: Instant) -> Option<TeardownCore> {
        match self.0 {
            Phase::Setup(c) => c.into_teardown(now),
            Phase::Playing(c) => c.into_setup().into_teardown(now),
            Phase::Switching => None,
        }
    }

    /// Returns true iff `PLAY` has succeeded (and the session hasn't since been
    /// torn down).
    #[inline]
    pub fn is_playing(&self) -> bool {
        matches!(self.0, Phase::Playing(_))
    }

    /// Returns a context for the RTSP connection, e.g. for error messages.
    pub fn conn_ctx(&self) -> &ConnectionContext {
        match &self.0 {
            Phase::Setup(c) => c.conn_ctx(),
            Phase::Playing(c) => c.conn_ctx(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns the buffer the caller should fill with bytes received on the
    /// RTSP connection, via `spare_capacity` and `advance_end`.
    #[inline]
    pub fn read_buf(&mut self) -> &mut MarkBuf {
        match &mut self.0 {
            Phase::Setup(c) => c.read_buf(),
            Phase::Playing(c) => c.read_buf(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Notes that the peer has closed the RTSP connection.
    ///
    /// A request awaiting its response then fails. While playing, once
    /// [`SessionCore::poll_item`] has returned the remaining items,
    /// [`SessionCore::is_closed`] is true.
    pub fn handle_eof(&mut self) {
        match &mut self.0 {
            Phase::Setup(c) => c.handle_eof(),
            Phase::Playing(c) => c.handle_eof(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns true if the peer has closed the RTSP connection.
    pub fn is_closed(&self) -> bool {
        match &self.0 {
            Phase::Setup(c) => c.is_closed(),
            Phase::Playing(c) => c.is_closed(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns an error for a failed read from the RTSP connection.
    pub fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        match &self.0 {
            Phase::Setup(c) => c.read_error(source, now),
            Phase::Playing(c) => c.read_error(source, now),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns the streams in the presentation; empty until
    /// [`SessionEvent::Described`].
    pub fn streams(&self) -> &[Stream] {
        match &self.0 {
            Phase::Setup(c) => c.streams(),
            Phase::Playing(c) => c.streams(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's
    /// `a:tool` SDP attribute.
    pub fn tool(&self) -> Option<&Tool> {
        match &self.0 {
            Phase::Setup(c) => c.tool(),
            Phase::Playing(c) => c.tool(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns the raw SDP from the `DESCRIBE` response; empty until
    /// [`SessionEvent::Described`].
    pub fn sdp(&self) -> &[u8] {
        match &self.0 {
            Phase::Setup(c) => c.sdp(),
            Phase::Playing(c) => c.sdp(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns the bytes to write to the RTSP connection, in order.
    ///
    /// The first slice is empty iff there's nothing to write. These are
    /// suitable for vectored I/O. After writing, call
    /// [`SessionCore::advance_transmit`]; bytes stay here until then.
    pub fn transmit_buf(&self) -> (&[u8], &[u8]) {
        match &self.0 {
            Phase::Setup(c) => c.transmit_buf(),
            Phase::Playing(c) => c.transmit_buf(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Notes that the first `n` bytes of [`SessionCore::transmit_buf`] have
    /// been written.
    ///
    /// Keepalive response timeouts start once the request has been written,
    /// so call this promptly after each write.
    ///
    /// # Panics
    ///
    /// If `n` exceeds the bytes available.
    pub fn advance_transmit(&mut self, n: usize) {
        match &mut self.0 {
            Phase::Setup(c) => c.advance_transmit(n),
            Phase::Playing(c) => c.advance_transmit(n),
            Phase::Switching => unreachable!(),
        }
    }

    /// Returns a packet to send on a UDP stream's socket, if any.
    ///
    /// Before `PLAY`, these punch holes in connection-tracking firewalls; send
    /// them once the stream's sockets are connected. While playing, these are
    /// RTCP receiver reports; send each right away if the socket has room and
    /// otherwise drop it, as later reports carry cumulative statistics anyway.
    pub fn poll_transmit_udp(&mut self) -> Option<UdpTransmit> {
        match &mut self.0 {
            Phase::Setup(c) => c.poll_transmit_udp(),
            Phase::Playing(c) => c.poll_transmit_udp(),
            Phase::Switching => unreachable!(),
        }
    }

    /// Starts a `DESCRIBE` request for `url`.
    ///
    /// `url` must use the `rtsp` scheme and must not contain credentials;
    /// supply those via [`SessionOptions::creds`].
    pub fn describe(&mut self, url: Url) -> Result<(), Error> {
        self.setup_core()?.describe(url)
    }

    /// Starts a `SETUP` request for stream `stream_i`.
    ///
    /// These can't reasonably be pipelined because subsequent requests are
    /// expected to adopt the previous response's `Session`. Likewise, the
    /// server may override the preferred interleaved channel id and it seems
    /// like a bad idea to try to assign more interleaved channels without
    /// inspecting that first.
    ///
    /// Panics if `stream_i >= self.streams().len()`.
    pub fn setup(&mut self, stream_i: usize, transport: SetupTransport) -> Result<(), Error> {
        self.setup_core()?.setup(stream_i, transport)
    }

    /// Starts a `PLAY` request for the entire presentation.
    ///
    /// The presentation must support aggregate control, as defined in [RFC 2326
    /// section 1.3](https://tools.ietf.org/html/rfc2326#section-1.3).
    pub fn play(&mut self, options: PlayOptions) -> Result<(), Error> {
        self.setup_core()?.play(options)
    }

    /// Starts a `TEARDOWN` request for the session.
    ///
    /// This can follow a failed request, but not one still in progress. If
    /// playing, the session stops: [`SessionCore::poll_item`] returns nothing
    /// more. Interleaved data and unrelated responses are ignored until the
    /// `TEARDOWN` response arrives via [`SessionCore::poll_event`].
    ///
    /// This is a single attempt, regardless of [`super::TeardownPolicy`]. To
    /// retry as a dropped [`super::Session`] does, use
    /// [`SessionCore::into_teardown`] instead.
    pub fn teardown(&mut self) -> Result<(), Error> {
        if let Phase::Playing(_) = self.0 {
            let Phase::Playing(c) = std::mem::replace(&mut self.0, Phase::Switching) else {
                unreachable!();
            };
            self.0 = Phase::Setup(c.into_setup());
        }
        self.setup_core()?.teardown()
    }

    /// Processes received data, returning the request which completed, if any.
    ///
    /// On error, the session should be abandoned (possibly after trying
    /// [`SessionCore::teardown`]). While playing, this returns `None`; use
    /// [`SessionCore::poll_item`] instead.
    pub fn poll_event(&mut self, now: Instant) -> Option<Result<SessionEvent, Error>> {
        let Phase::Setup(c) = &mut self.0 else {
            return None;
        };
        let r = c.poll_event(now)?;
        if matches!(r, Ok(SessionEvent::Playing)) {
            let Phase::Setup(c) = std::mem::replace(&mut self.0, Phase::Switching) else {
                unreachable!();
            };
            self.0 = Phase::Playing(c.into_playing(now));
        }
        Some(r)
    }

    /// While playing, parses and validates the next packet from buffered data.
    ///
    /// Returns `None` when more data is needed (or, if
    /// [`SessionCore::is_closed`], never will be), or if not playing. Handles
    /// keepalive responses internally.
    ///
    /// The item borrows the core, so it must be dropped before the next call.
    pub fn poll_item(&mut self, now: Instant) -> Option<Result<super::PlayingItem<'_>, Error>> {
        match &mut self.0 {
            Phase::Playing(c) => c.poll_item(now),
            _ => None,
        }
    }

    /// Returns true if `stream_i` is playing via UDP, so its sockets should
    /// be read into [`SessionCore::udp_buf`].
    pub fn is_udp(&self, stream_i: usize) -> bool {
        self.playing().is_some_and(|c| c.is_udp(stream_i))
    }

    /// Returns the buffer the caller should read a datagram for UDP stream
    /// `stream_i` into, via `spare_capacity`. Follow with
    /// [`SessionCore::udp_received`].
    ///
    /// Panics unless [`SessionCore::is_udp`].
    pub fn udp_buf(&mut self, stream_i: usize) -> &mut MarkBuf {
        self.playing_mut()
            .expect("udp_buf requires a playing session")
            .udp_buf(stream_i)
    }

    /// Notes that a `len`-byte datagram was written to the start of
    /// [`SessionCore::udp_buf`]'s spare capacity.
    ///
    /// The caller may receive several datagrams before calling
    /// [`SessionCore::poll_item`]; they stay in the buffer until parsed.
    ///
    /// Panics unless [`SessionCore::is_udp`].
    pub fn udp_received(
        &mut self,
        stream_i: usize,
        channel_type: ChannelType,
        len: u16,
        now: Instant,
    ) {
        self.playing_mut()
            .expect("udp_received requires a playing session")
            .udp_received(stream_i, channel_type, len, now)
    }

    /// Returns an error for a failed receive on UDP stream `stream_i`.
    pub fn udp_recv_error(&self, stream_i: usize, source: std::io::Error) -> Error {
        match self.playing() {
            Some(c) => c.udp_recv_error(stream_i, source),
            None => wrap!(ErrorInt::UdpRecvError {
                conn_ctx: *self.conn_ctx(),
                stream_ctx: StreamContext::dummy(),
                when: WallTime::now(),
                source,
            }),
        }
    }

    /// Returns the next time [`SessionCore::handle_timeout`] should be
    /// called, if any. This is `None` until playing.
    pub fn poll_timeout(&self) -> Option<Instant> {
        self.playing().map(PlayingCore::poll_timeout)
    }

    /// Handles the passage of time, starting a keepalive request and/or
    /// writing receiver reports if due.
    ///
    /// Returns an error if the previous keepalive hasn't been flushed or
    /// answered in time.
    pub fn handle_timeout(&mut self, now: Instant) -> Result<(), Error> {
        match self.playing_mut() {
            Some(c) => c.handle_timeout(now),
            None => Ok(()),
        }
    }

    /// While playing, queues an RTP packet on a
    /// [`super::StreamDirection::Sending`] stream (ONVIF backchannel), for
    /// [`SessionCore::transmit_buf`].
    ///
    /// The caller builds packets with its own [`crate::rtp::Sender`], created
    /// with the stream's [`Stream::rtp_payload_type`], and sends RTCP sender
    /// reports for it via [`SessionCore::queue_rtcp`].
    ///
    /// This doesn't limit how much is queued. A caller sending live media
    /// should check [`SessionCore::queued_len`] first and drop media (or,
    /// via [`crate::codec::PayloadSink::congested`], have a packetizer shed
    /// load) while the server reads slowly, rather than wait, so sent media
    /// stays close to real time and the session keeps reading. After dropping
    /// a packet, [`crate::rtp::Sender::skip`] shows the gap to the server.
    ///
    /// Fails without queueing anything if the session isn't playing or the
    /// stream isn't set up for sending; the session is still usable.
    #[cfg(feature = "unstable-send")]
    pub fn queue_rtp(
        &mut self,
        stream_i: usize,
        pkt: &crate::rtp::OutgoingPacketRef<'_>,
    ) -> Result<(), Error> {
        match self.playing_mut() {
            Some(c) => c.queue_rtp(stream_i, pkt),
            None => bail!(ErrorInt::FailedPrecondition(
                "can't send before PLAY".into()
            )),
        }
    }

    /// While playing, queues an RTCP packet, such as a sender report from
    /// [`crate::rtp::Sender::sender_report`], on a
    /// [`super::StreamDirection::Sending`] stream, for
    /// [`SessionCore::transmit_buf`].
    ///
    /// Fails as [`SessionCore::queue_rtp`] does, or if `pkt` is longer than
    /// 65,535 bytes.
    #[cfg(feature = "unstable-send")]
    pub fn queue_rtcp(&mut self, stream_i: usize, pkt: &[u8]) -> Result<(), Error> {
        match self.playing_mut() {
            Some(c) => c.queue_rtcp(stream_i, pkt),
            None => bail!(ErrorInt::FailedPrecondition(
                "can't send before PLAY".into()
            )),
        }
    }

    /// Returns the number of bytes in [`SessionCore::transmit_buf`], e.g. to
    /// decide whether to queue more media via [`SessionCore::queue_rtp`].
    #[cfg(feature = "unstable-send")]
    pub fn queued_len(&self) -> usize {
        let (a, b) = self.transmit_buf();
        a.len() + b.len()
    }
}

#[rustfmt::skip]
pub(crate) const HOLE_PUNCH_RTP: [u8; 12] = [
    2 << 6,     // version=2 + p=0 + x=0 + cc=0
    0,          // m=0 + pt=0
    0, 0,       // sequence number=0
    0, 0, 0, 0, // timestamp=0 0,
    0, 0, 0, 0, // ssrc=0
];
#[rustfmt::skip]
pub(crate) const HOLE_PUNCH_RTCP: [u8; 8] = [
    2 << 6,     // version=2 + p=0 + rc=0
    201,        // pt=200 (reception report)
    0, 1,       // length=1 (in 4-byte words minus 1)
    0, 0, 0, 0, // ssrc=0 (bogus but we don't know the ssrc reliably yet)
];

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::teardown::TeardownAction;
    use crate::client::{Credentials, PlayingItem};
    use std::sync::Arc;

    const EXISTING_CONN_TIMEOUT_FOR_TEST: Duration = Duration::from_secs(5);

    fn new_core(options: SessionOptions) -> SessionCore {
        crate::testutil::init_logging();
        SessionCore::new(
            "192.168.1.210:40000".parse().unwrap(),
            "192.168.5.206:554".parse().unwrap(),
            options,
        )
    }

    fn url() -> Url {
        Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap()
    }

    /// Returns the single request the core wants to send, marking it written.
    fn transmitted(core: &mut SessionCore) -> msg::Request {
        let (a, b) = core.transmit_buf();
        let data = [a, b].concat();
        core.advance_transmit(data.len());
        parse_request(&data)
    }

    /// Parses `data`, which should be exactly one request.
    fn parse_request(data: &[u8]) -> msg::Request {
        assert!(!data.is_empty(), "should transmit");
        let mut input = data;
        let (msg, _) = crate::rtsp::parse::Parser::default()
            .feed(&mut input)
            .unwrap()
            .unwrap();
        assert!(input.is_empty());
        match msg {
            msg::Message::Request(r) => r,
            o => panic!("expected request, got {o:#?}"),
        }
    }

    /// Answers the pending request (of method `method`) with the response in
    /// `raw`, with its `CSeq` changed to match.
    fn respond(core: &mut SessionCore, method: msg::Method, raw: &'static [u8]) -> msg::Request {
        let req = transmitted(core);
        assert_eq!(req.method, method);
        core.read_buf().extend(&response_to(&req, raw));
        req
    }

    /// Returns the response in `raw` to `req`, with its `CSeq` changed to
    /// match.
    fn response_to(req: &msg::Request, raw: &'static [u8]) -> Vec<u8> {
        let (mut head, body) = crate::testutil::response(raw);
        head.headers.insert(
            msg::HeaderName::CSEQ,
            req.headers.get("CSeq").unwrap().clone(),
        );
        let mut data = Vec::new();
        OwnedMessage::Response { head, body }
            .write(&mut data)
            .unwrap();
        data
    }

    /// Returns a core playing stream 0 via TCP, with the given test data.
    fn playing(
        options: SessionOptions,
        describe: &'static [u8],
        setup: &'static [u8],
        play: &'static [u8],
        now: Instant,
    ) -> SessionCore {
        let mut core = new_core(options);
        core.describe(url()).unwrap();
        respond(&mut core, msg::Method::DESCRIBE, describe);
        core.poll_event(now).unwrap().unwrap();
        core.setup(0, SetupTransport::Tcp).unwrap();
        respond(&mut core, msg::Method::SETUP, setup);
        core.poll_event(now).unwrap().unwrap();
        core.play(PlayOptions::default()).unwrap();
        respond(&mut core, msg::Method::PLAY, play);
        assert!(matches!(
            core.poll_event(now),
            Some(Ok(SessionEvent::Playing))
        ));
        core
    }

    /// Returns a core playing a Reolink camera, which advertises a live555
    /// version with the stale TCP session bug.
    fn playing_reolink(options: SessionOptions, now: Instant) -> SessionCore {
        playing(
            options,
            include_bytes!("testdata/reolink_describe.txt"),
            include_bytes!("testdata/reolink_setup.txt"),
            include_bytes!("testdata/reolink_play.txt"),
            now,
        )
    }

    /// Returns the single request the teardown core wants to send, marking it
    /// written.
    fn teardown_transmitted(td: &mut TeardownCore) -> msg::Request {
        let (a, b) = td.transmit_buf();
        let data = [a, b].concat();
        td.advance_transmit(data.len());
        let req = parse_request(&data);
        assert_eq!(req.method, msg::Method::TEARDOWN);
        req
    }

    fn server_addrs() -> (SocketAddr, SocketAddr) {
        (
            "192.168.1.210:40001".parse().unwrap(),
            "192.168.5.206:554".parse().unwrap(),
        )
    }

    /// Returns the outcome of `SessionGroup::await_teardown` if it's ready.
    fn await_teardown_now(group: &super::super::SessionGroup) -> Option<Result<(), Error>> {
        use futures::FutureExt as _;
        group.await_teardown().now_or_never()
    }

    /// The first `TEARDOWN` goes on the session's connection, after bytes
    /// not yet written, and succeeds.
    #[test]
    fn teardown_on_existing_conn() {
        let group = Arc::new(super::super::SessionGroup::default());
        let t0 = Instant::now();
        let core = playing_reolink(SessionOptions::default().session_group(group.clone()), t0);
        assert_eq!(group.stale_sessions(t0).num_sessions, 0);
        let mut td = core.into_teardown(t0).unwrap();
        let status = group.stale_sessions(t0);
        assert_eq!(status.num_sessions, 1);
        assert_eq!(status.max_expires, Some(t0 + Duration::from_secs(60)));
        assert_eq!(td.expires(), t0 + Duration::from_secs(60));
        assert!(await_teardown_now(&group).is_none());

        let TeardownAction::Io { deadline } = td.poll(t0) else {
            panic!("expected Io");
        };
        assert_eq!(deadline, t0 + EXISTING_CONN_TIMEOUT_FOR_TEST);
        let req = teardown_transmitted(&mut td);
        assert_eq!(req.headers.get("Session").unwrap().to_string(), "F8F8E425");
        assert_eq!(req.headers.get("CSeq").unwrap().to_string(), "4");
        assert!(matches!(td.poll(t0), TeardownAction::Io { .. }));

        // Interleaved data and the response arrive.
        let mut data = Vec::new();
        OwnedMessage::Data {
            channel_id: 0,
            body: Bytes::from_static(b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8"),
        }
        .write(&mut data)
        .unwrap();
        data.extend(response_to(
            &req,
            include_bytes!("testdata/reolink_teardown.txt"),
        ));
        td.read_buf().extend(&data);
        assert!(matches!(td.poll(t0), TeardownAction::Done));
        assert!(matches!(td.poll(t0), TeardownAction::Done));
        assert_eq!(group.stale_sessions(t0).num_sessions, 0);
        assert!(matches!(await_teardown_now(&group), Some(Ok(()))));
    }

    /// With the live555 bug, failed attempts are retried on fresh
    /// connections, backing off with growing timeouts.
    #[test]
    fn teardown_retries_on_fresh_conns() {
        let group = Arc::new(super::super::SessionGroup::default());
        let t0 = Instant::now();
        let core = playing_reolink(SessionOptions::default().session_group(group.clone()), t0);
        let mut td = core.into_teardown(t0).unwrap();
        assert!(matches!(td.poll(t0), TeardownAction::Io { .. }));

        // The server closes the session's connection. A fresh one is due
        // right away. That failure isn't reported to the group.
        td.handle_eof();
        let TeardownAction::Connect { deadline } = td.poll(t0) else {
            panic!("expected Connect");
        };
        assert_eq!(deadline, t0 + Duration::from_secs(1));
        assert!(await_teardown_now(&group).is_none());
        assert!(td.transmit_buf().0.is_empty());

        // Attempt 1 fails quickly, so the next waits for its deadline.
        let (local, peer) = server_addrs();
        td.connected(local, peer, t0);
        let req = teardown_transmitted(&mut td);
        assert_eq!(req.headers.get("CSeq").unwrap().to_string(), "1");
        td.handle_io_error(std::io::ErrorKind::ConnectionReset.into(), t0);
        let e = await_teardown_now(&group).unwrap().unwrap_err();
        assert!(e.to_string().contains("connection reset"), "{e}");
        assert!(matches!(
            td.poll(t0),
            TeardownAction::Wait { until } if until == t0 + Duration::from_secs(1)
        ));

        // Attempt 2 times out while connecting; attempt 3 starts right away.
        let t1 = t0 + Duration::from_secs(1);
        let TeardownAction::Connect { deadline } = td.poll(t1) else {
            panic!("expected Connect");
        };
        assert_eq!(deadline, t1 + Duration::from_secs(2));
        let t2 = deadline;
        let TeardownAction::Connect { deadline } = td.poll(t2) else {
            panic!("expected Connect");
        };
        assert_eq!(deadline, t2 + Duration::from_secs(4));

        // Attempt 3 succeeds.
        td.connected(local, peer, t2);
        let req = teardown_transmitted(&mut td);
        td.read_buf().extend(&response_to(
            &req,
            include_bytes!("testdata/reolink_teardown.txt"),
        ));
        assert!(matches!(td.poll(t2), TeardownAction::Done));
        assert_eq!(group.stale_sessions(t2).num_sessions, 0);
        assert!(matches!(await_teardown_now(&group), Some(Ok(()))));
    }

    /// Without the live555 bug, a TCP session gets one attempt, on its own
    /// connection.
    #[test]
    fn teardown_tcp_tries_once() {
        let group = Arc::new(super::super::SessionGroup::default());
        let t0 = Instant::now();
        let core = playing(
            SessionOptions::default().session_group(group.clone()),
            include_bytes!("testdata/hikvision_describe.txt"),
            include_bytes!("testdata/hikvision_setup.txt"),
            include_bytes!("testdata/hikvision_play.txt"),
            t0,
        );
        let mut td = core.into_teardown(t0).unwrap();
        let TeardownAction::Io { deadline } = td.poll(t0) else {
            panic!("expected Io");
        };
        teardown_transmitted(&mut td);
        assert!(matches!(td.poll(deadline), TeardownAction::Done));
        assert_eq!(group.stale_sessions(deadline).num_sessions, 0);
        assert!(matches!(await_teardown_now(&group), Some(Ok(()))));
    }

    /// Retries stop at the session's expiration, when the group forgets it.
    #[test]
    fn teardown_expires() {
        let group = Arc::new(super::super::SessionGroup::default());
        let t0 = Instant::now();
        let core = playing_reolink(
            SessionOptions::default()
                .session_group(group.clone())
                .teardown(TeardownPolicy::Always),
            t0,
        );
        let mut td = core.into_teardown(t0).unwrap();
        let expires = td.expires();
        let mut now = t0;
        let mut attempts = 0;
        loop {
            match td.poll(now) {
                TeardownAction::Io { deadline } | TeardownAction::Connect { deadline } => {
                    assert!(deadline <= expires);
                    attempts += 1;
                    now = deadline;
                }
                TeardownAction::Wait { until } => now = until,
                TeardownAction::Done => break,
            }
        }
        assert_eq!(now, expires);
        // 5 s on the existing connection, then fresh connection attempts of 1,
        // 2, 4, 8, 16, 16, and (cut short by the 60 s timeout) 16 s.
        assert_eq!(attempts, 8);
        assert_eq!(group.stale_sessions(now).num_sessions, 0);
        assert!(matches!(await_teardown_now(&group), Some(Ok(()))));
    }

    /// Dropping a teardown core early counts as failure, and the session stays
    /// tracked until it expires.
    #[test]
    fn teardown_abandoned() {
        let group = Arc::new(super::super::SessionGroup::default());
        let t0 = Instant::now();
        let core = playing_reolink(SessionOptions::default().session_group(group.clone()), t0);
        let td = core.into_teardown(t0).unwrap();
        let expires = td.expires();
        drop(td);
        assert!(matches!(await_teardown_now(&group), Some(Err(_))));
        assert_eq!(group.stale_sessions(t0).num_sessions, 1);
        assert_eq!(group.stale_sessions(expires).num_sessions, 0);
    }

    /// Nothing to tear down without `SETUP`, or with `TeardownPolicy::Never`.
    #[test]
    fn teardown_unneeded() {
        let t0 = Instant::now();
        let mut core = new_core(SessionOptions::default());
        core.describe(url()).unwrap();
        assert!(core.into_teardown(t0).is_none());
        let core = playing_reolink(
            SessionOptions::default().teardown(TeardownPolicy::Never),
            t0,
        );
        assert!(core.into_teardown(t0).is_none());
    }

    /// Drives a TCP session through `DESCRIBE`, `SETUP`, `PLAY`, a packet,
    /// and `TEARDOWN`, with no sockets.
    #[test]
    fn tcp_lifecycle() {
        let mut core = new_core(SessionOptions::default());
        let t0 = Instant::now();
        core.describe(url()).unwrap();
        assert!(core.poll_event(t0).is_none(), "no response yet");
        respond(
            &mut core,
            msg::Method::DESCRIBE,
            include_bytes!("testdata/reolink_describe.txt"),
        );
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::Described))
        ));
        assert_eq!(core.streams().len(), 2);
        assert!(core.sdp().starts_with(b"v=0"));

        core.setup(0, SetupTransport::Tcp).unwrap();
        let req = respond(
            &mut core,
            msg::Method::SETUP,
            include_bytes!("testdata/reolink_setup.txt"),
        );
        assert_eq!(
            &*req.headers.get("Transport").unwrap().to_string(),
            "RTP/AVP/TCP;unicast;interleaved=0-1"
        );
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::SetUp {
                stream_i: 0,
                udp_peer: None
            }))
        ));
        assert!(core.streams()[0].is_setup());

        core.play(PlayOptions::default()).unwrap();
        let req = respond(
            &mut core,
            msg::Method::PLAY,
            include_bytes!("testdata/reolink_play.txt"),
        );
        assert_eq!(req.headers.get("Session").unwrap().to_string(), "F8F8E425");

        // A packet which arrives right behind the `PLAY` response is kept for
        // the playing core.
        let pkt = b"\x80\x60\x41\xd4\x00\x00\x00\x00\xdc\xc4\xa0\xd8hello world";
        let mut data = Vec::new();
        OwnedMessage::Data {
            channel_id: 0,
            body: Bytes::from_static(pkt),
        }
        .write(&mut data)
        .unwrap();
        core.read_buf().extend(&data);
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::Playing))
        ));
        assert!(core.is_playing());
        assert!(core.poll_event(t0).is_none());
        assert!(core.poll_timeout().is_some());
        match core.poll_item(t0) {
            Some(Ok(PlayingItem::Rtp(p))) => {
                assert_eq!(p.stream_id(), 0);
                assert_eq!(p.packet().meta.sequence_number, 0x41d4);
                assert_eq!(p.packet().payload().to_vec(), b"hello world");
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        assert!(core.poll_item(t0).is_none());
        let e = core.setup(1, SetupTransport::Tcp).unwrap_err();
        assert!(e.to_string().contains("already playing"), "{e}");

        // The `TEARDOWN` stops playing and ignores interleaved data.
        core.teardown().unwrap();
        assert!(!core.is_playing());
        core.read_buf().extend(&data);
        let req = respond(
            &mut core,
            msg::Method::TEARDOWN,
            include_bytes!("testdata/reolink_teardown.txt"),
        );
        assert_eq!(req.headers.get("Session").unwrap().to_string(), "F8F8E425");
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::TornDown))
        ));
        assert!(core.poll_item(t0).is_none());
    }

    /// Drives an ONVIF backchannel session with no sockets: the `Require`
    /// header on `DESCRIBE`, the backchannel's `SETUP`, `PLAY`, and
    /// `TEARDOWN`, and media queued for the transmit buffer.
    #[cfg(feature = "unstable-send")]
    #[test]
    fn backchannel_lifecycle() {
        fn require(req: &msg::Request) -> Option<String> {
            req.headers.get("Require").map(|v| v.to_string())
        }
        const REQUIRE: Option<&str> = Some("www.onvif.org/ver20/backchannel");
        let mut core = new_core(SessionOptions::default().backchannel(true));
        let t0 = Instant::now();
        core.describe(Url::parse("rtsp://192.168.0.1/").unwrap())
            .unwrap();
        let req = respond(
            &mut core,
            msg::Method::DESCRIBE,
            include_bytes!("testdata/onvif_backchannel_describe.txt"),
        );
        assert_eq!(require(&req).as_deref(), REQUIRE);
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::Described))
        ));
        assert_eq!(
            core.streams()[2].direction(),
            super::super::StreamDirection::Sending
        );
        let mut sender = crate::rtp::Sender::new(
            core.streams()[2].rtp_payload_type(),
            crate::rtp::SenderOptions::default(),
        );
        let ts =
            |t| crate::Timestamp::new(t, std::num::NonZeroU32::new(8_000).unwrap(), 0).unwrap();
        let e = core.queue_rtp(2, &sender.packet(ts(0), false, &[b"x"]));
        assert!(e.unwrap_err().to_string().contains("before PLAY"));

        let e = core
            .setup(
                2,
                SetupTransport::Udp {
                    client_rtp_port: 5000,
                },
            )
            .unwrap_err();
        assert!(matches!(*e.0, ErrorInt::Unsupported(_)), "{e}");
        core.setup(2, SetupTransport::Tcp).unwrap();
        let req = respond(
            &mut core,
            msg::Method::SETUP,
            b"RTSP/1.0 200 OK\r\n\
              CSeq: 0\r\n\
              Session: 12345678;timeout=60\r\n\
              Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n",
        );
        assert_eq!(require(&req).as_deref(), REQUIRE);
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::SetUp { stream_i: 2, .. }))
        ));

        core.play(PlayOptions::default()).unwrap();
        let req = respond(
            &mut core,
            msg::Method::PLAY,
            b"RTSP/1.0 200 OK\r\nCSeq: 0\r\nSession: 12345678\r\n\r\n",
        );
        assert_eq!(require(&req).as_deref(), REQUIRE);
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::Playing))
        ));

        // RTP and RTCP go on the stream's interleaved channels.
        core.queue_rtp(2, &sender.packet(ts(0), true, &[&[0xff; 100], &[0xff; 60]]))
            .unwrap();
        let sr = sender.sender_report(crate::NtpTimestamp(0), ts(0), "cname");
        core.queue_rtcp(2, &sr).unwrap();
        assert_eq!(core.queued_len(), 4 + 12 + 160 + 4 + sr.len());
        let (a, b) = core.transmit_buf();
        let data = [a, b].concat();
        core.advance_transmit(data.len());
        assert_eq!(core.queued_len(), 0);
        assert_eq!(&data[..4], b"$\x00\x00\xac"); // channel 0, 12 + 160 bytes.
        assert_eq!(data[5], 0x80); // marker bit, payload type 0.
        assert_eq!(&data[176..178], b"$\x01");
        assert_eq!(data[181], 200); // sender report.
        assert_eq!(&data[180..], &sr[..]);

        // Too-long RTCP isn't queued.
        let e = core.queue_rtcp(2, &[0; 65_536]).unwrap_err();
        assert!(matches!(*e.0, ErrorInt::InvalidArgument(_)), "{e}");
        assert_eq!(core.queued_len(), 0);

        core.teardown().unwrap();
        let req = respond(
            &mut core,
            msg::Method::TEARDOWN,
            b"RTSP/1.0 200 OK\r\nCSeq: 0\r\nSession: 12345678\r\n\r\n",
        );
        assert_eq!(require(&req).as_deref(), REQUIRE);
    }

    /// A `401 Unauthorized` causes a retry with Digest authentication.
    #[test]
    fn auth_retry() {
        let mut core = new_core(SessionOptions::default().creds(Some(Credentials {
            username: "admin".to_owned(),
            password: "secret".to_owned(),
        })));
        let t0 = Instant::now();
        core.describe(url()).unwrap();
        let req = respond(
            &mut core,
            msg::Method::DESCRIBE,
            include_bytes!("testdata/longse_unauthorized.txt"),
        );
        assert!(req.headers.get("Authorization").is_none());
        assert!(core.poll_event(t0).is_none(), "should retry");
        let req = respond(
            &mut core,
            msg::Method::DESCRIBE,
            include_bytes!("testdata/reolink_describe.txt"),
        );
        let authorization = req.headers.get("Authorization").unwrap().to_string();
        assert!(authorization.starts_with("Digest "), "{authorization}");
        assert_eq!(req.headers.get("CSeq").unwrap().to_string(), "2");
        assert!(matches!(
            core.poll_event(t0),
            Some(Ok(SessionEvent::Described))
        ));
    }

    /// A UDP `SETUP` returns the server's address and queues hole-punching
    /// packets.
    #[test]
    fn udp_setup() {
        let mut core = new_core(SessionOptions::default());
        let t0 = Instant::now();
        core.describe(url()).unwrap();
        respond(
            &mut core,
            msg::Method::DESCRIBE,
            include_bytes!("testdata/reolink_describe.txt"),
        );
        core.poll_event(t0).unwrap().unwrap();
        core.setup(
            1,
            SetupTransport::Udp {
                client_rtp_port: 54060,
            },
        )
        .unwrap();
        let req = respond(
            &mut core,
            msg::Method::SETUP,
            include_bytes!("testdata/luckfox_rkipc_setup_udp.txt"),
        );
        assert_eq!(
            &*req.headers.get("Transport").unwrap().to_string(),
            "RTP/AVP/UDP;unicast;client_port=54060-54061"
        );
        let Some(Ok(SessionEvent::SetUp { stream_i, udp_peer })) = core.poll_event(t0) else {
            panic!("expected SetUp");
        };
        assert_eq!(stream_i, 1);
        assert_eq!(udp_peer, Some("192.168.5.206:49152".parse().unwrap()));
        let t = core.poll_transmit_udp().unwrap();
        assert_eq!((t.stream_i, t.channel_type), (1, ChannelType::Rtp));
        assert_eq!(t.data, HOLE_PUNCH_RTP);
        let t = core.poll_transmit_udp().unwrap();
        assert_eq!((t.stream_i, t.channel_type), (1, ChannelType::Rtcp));
        assert!(core.poll_transmit_udp().is_none());
    }

    #[test]
    fn one_request_at_a_time() {
        let mut core = new_core(SessionOptions::default());
        core.describe(url()).unwrap();
        let e = core.describe(url()).unwrap_err();
        assert!(e.to_string().contains("in progress"), "{e}");
    }

    #[test]
    fn eof_while_waiting() {
        let mut core = new_core(SessionOptions::default());
        core.describe(url()).unwrap();
        core.read_buf().extend(b"RTSP/1.0 200 OK\r\n");
        core.handle_eof();
        let Some(Err(e)) = core.poll_event(Instant::now()) else {
            panic!("expected error");
        };
        assert!(
            e.to_string().contains("Incomplete RTSP message at EOF"),
            "{e}"
        );
    }

    #[test]
    fn validate_hole_punch_rtp() {
        let (header, _) = crate::rtp::PacketHeader::validate(&HOLE_PUNCH_RTP[..]).unwrap();
        assert_eq!(header.payload_type(), 0);
    }

    #[test]
    fn validate_hole_punch_rtcp() {
        let (pkt_ref, _) = crate::rtcp::PacketRef::parse(&HOLE_PUNCH_RTCP[..]).unwrap();
        assert!(matches!(
            pkt_ref.as_typed().unwrap(),
            Some(crate::rtcp::TypedPacketRef::ReceiverReport(_))
        ));
    }
}
