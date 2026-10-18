// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The sans-I/O core of a session; see [`SessionCore`].

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
use super::{
    InitialSequenceNumberPolicy, InitialTimestampPolicy, PlayOptions, Presentation, SessionFlag,
    SessionIdPolicy, SessionOptions, Stream, StreamState, StreamStateInit, Tool,
    UnknownRtcpSsrcPolicy, receiver_report, rtp,
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
    Udp {
        client_rtp_port: u16,
        options: super::UdpTransportOptions,
    },
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
        reorder: Option<crate::rtp::ReorderOptions>,
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

    pub(crate) fn into_parts(self) -> (ConnCore, Option<Presentation>, Option<SessionHeader>, u8) {
        (self.conn, self.presentation, self.session, self.flags)
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

    /// Returns bytes to write to the RTSP connection, if any.
    ///
    /// Each call returns new bytes, to be written after those from earlier
    /// calls.
    pub(crate) fn poll_transmit(&mut self) -> Option<Vec<u8>> {
        self.conn.poll_transmit()
    }

    /// Returns a packet to send on a UDP stream's socket, if any.
    pub(crate) fn poll_transmit_udp(&mut self) -> Option<UdpTransmit> {
        self.transmit_udp.pop_front()
    }

    pub(crate) fn session(&self) -> Option<&SessionHeader> {
        self.session.as_ref()
    }

    pub(crate) fn flags(&self) -> u8 {
        self.flags
    }

    pub(crate) fn options(&self) -> &SessionOptions {
        &self.conn.options
    }

    pub(crate) fn base_url(&self) -> Option<&Url> {
        self.presentation.as_ref().map(|p| &p.base_url)
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
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::DESCRIBE,
                request_uri: Some(url.clone()),
                headers: [(
                    msg::HeaderName::ACCEPT,
                    msg::HeaderValue::try_from("application/sdp").unwrap(),
                )]
                .into(),
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
        let url = stream
            .control
            .as_ref()
            .unwrap_or(&presentation.control)
            .clone();
        let mut headers = msg::Headers::default();
        let mut reorder = None;
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
            SetupTransport::Udp {
                client_rtp_port,
                options,
            } => {
                reorder = Some(options.reorder);
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
        self.start(
            ResponseMode::Normal,
            Op::Setup {
                stream_i,
                udp,
                reorder,
            },
            req,
        )?;
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
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::PLAY,
                request_uri: Some(presentation.control.clone()),
                headers: [
                    (msg::HeaderName::SESSION, session.id.clone()),
                    (
                        msg::HeaderName::RANGE,
                        msg::HeaderValue::try_from("npt=0.000-").unwrap(),
                    ),
                ]
                .into(),
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
        let (Some(presentation), Some(session)) = (&self.presentation, &self.session) else {
            bail!(ErrorInt::FailedPrecondition(
                "no session to tear down".into()
            ));
        };
        let req = OwnedMessage::Request {
            head: msg::Request {
                method: msg::Method::TEARDOWN,
                request_uri: Some(presentation.base_url.clone()),
                headers: [(msg::HeaderName::SESSION, session.id.clone())].into(),
            },
            body: Bytes::new(),
        };
        self.start(ResponseMode::Teardown, Op::Teardown, req)
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
            (_, Err(e)) => Err(e),
            (Op::Describe { url }, Ok(r)) => self.handle_describe(url, r),
            (
                Op::Setup {
                    stream_i,
                    udp,
                    reorder,
                },
                Ok(r),
            ) => self.handle_setup(stream_i, udp, reorder, r),
            (Op::Play { options }, Ok(r)) => self.handle_play(options, r),
        })
    }

    fn handle_describe(
        &mut self,
        url: Url,
        r: super::conn::Response,
    ) -> Result<SessionEvent, Error> {
        let presentation = parse::parse_describe(url, &r.head, &r.body)
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
        reorder: Option<crate::rtp::ReorderOptions>,
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
        stream.state = StreamState::Init(StreamStateInit {
            ssrc: response.ssrc,
            initial_seq: None,
            initial_rtptime: None,
            ctx,
            reorder: reorder.filter(|_| udp_peer.is_some()),
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

        // Count how many streams have been setup (not how many are in the presentation).
        let setup_streams = presentation
            .streams
            .iter()
            .filter(|s| matches!(s.state, StreamState::Init(_)))
            .count();

        let all_have_time = presentation.streams.iter().all(|s| match s.state {
            StreamState::Init(StreamStateInit {
                initial_rtptime, ..
            }) => initial_rtptime.is_some(),
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
                reorder,
            }) = s.state
            else {
                continue;
            };
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
                .learn_ssrc_from_sender_report(!matches!(
                    policy.unknown_rtcp_ssrc,
                    UnknownRtcpSsrcPolicy::ProcessPackets
                ));
            // TCP doesn't reorder packets, so it doesn't wait for them. Its
            // reorderer still drops late packets and recognizes restarts.
            let mut reorder = reorder
                .unwrap_or_else(|| crate::rtp::ReorderOptions::default().max_delay(Duration::ZERO));
            if let Some(ssrc) = ssrc {
                options = options.ssrc(ssrc);
            }
            if let Some(seq) = initial_seq {
                options = options.initial_sequence_number(seq);
                reorder = reorder.initial_sequence_number(seq);
            }
            if let Some(rtptime) = initial_rtptime {
                options = options.initial_rtptime(rtptime);
            }
            let receiver = crate::rtp::Receiver::new(s.clock_rate_hz, options)
                .map_err(|e| r.error(&conn_ctx, e.to_string()))?;
            core_streams[i] = Some(PlayingStream {
                rtp_handler: rtp::StreamReceiver::new(receiver, policy.unknown_rtcp_ssrc),
                reorderer: crate::rtp::Reorderer::new(reorder),
                ctx,
                udp_buf: matches!(ctx.0, StreamContextInner::Udp(_)).then(|| MarkBuf::new(65536)),
                reception: self
                    .conn
                    .options
                    .receiver_reports
                    .enabled()
                    .then(|| receiver_report::ReceptionStats::new(s.clock_rate_hz)),
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
/// *   writes the bytes from [`SessionCore::poll_transmit`] to the RTSP
///     connection.
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
/// *   calls [`SessionCore::handle_timeout`] at [`SessionCore::poll_timeout`],
///     for keepalives and RTCP receiver reports, and
///     [`SessionCore::handle_flushed`] after writing everything from
///     [`SessionCore::poll_transmit`]. Keepalives keep the session alive only
///     as long as the caller does all this, so it shouldn't stall on handling
///     items.
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
    pub(crate) fn take_setup(&mut self) -> Option<SetupCore> {
        match std::mem::replace(&mut self.0, Phase::Switching) {
            Phase::Setup(c) => Some(c),
            Phase::Playing(c) => Some(c.into_setup()),
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

    /// Returns bytes to write to the RTSP connection, if any.
    ///
    /// Each call returns new bytes, to be written after those from earlier
    /// calls.
    pub fn poll_transmit(&mut self) -> Option<Vec<u8>> {
        match &mut self.0 {
            Phase::Setup(c) => c.poll_transmit(),
            Phase::Playing(c) => c.poll_transmit(),
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

    /// Notes that all bytes returned by [`SessionCore::poll_transmit`] have
    /// been written.
    pub fn handle_flushed(&mut self) {
        if let Some(c) = self.playing_mut() {
            c.handle_flushed();
        }
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
    use crate::client::{Credentials, PlayingItem};

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

    /// Returns the single request the core wants to send.
    fn transmitted(core: &mut SessionCore) -> msg::Request {
        let data = core.poll_transmit().expect("should transmit");
        assert!(core.poll_transmit().is_none());
        let mut input = &data[..];
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
        let (mut head, body) = crate::testutil::response(raw);
        head.headers.insert(
            msg::HeaderName::CSEQ,
            req.headers.get("CSeq").unwrap().clone(),
        );
        let mut data = Vec::new();
        OwnedMessage::Response { head, body }
            .write(&mut data)
            .unwrap();
        core.read_buf().extend(&data);
        req
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
                options: Default::default(),
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
