// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Experimental RTSP server support.
//!
//! [`ConnectionCore`] is the sans-I/O state of one RTSP server connection:
//! it parses requests, answers the ones it can itself, and surfaces the
//! rest as [`Event`]s for the application to answer. Only RTP/AVP/TCP
//! (interleaved) transport is supported so far.
//!
//! Sending media is up to the caller: see [`crate::codec::VideoPacketizer`]
//! and [`crate::rtp::Sender`]. The `proxy` example ties these together.
//!
//! This API is a prototype, exempt from semver, and likely to change in any
//! release.

use std::collections::VecDeque;
use std::fmt::Write as _;
use std::io::Write as _;
use std::net::SocketAddr;
use std::sync::{Arc, Weak};
use std::time::{Duration, Instant};

use url::Url;

use crate::buf::MarkBuf;
use crate::rtsp::msg::{self, HeaderName, HeaderValue, StatusCode};
use crate::rtsp::reader::Reader;
use crate::rtsp::transmit::TransmitBuf;
use crate::{ConnectionContext, WallTime};

/// Options for a [`ConnectionCore`].
#[derive(Clone, Debug)]
pub struct ServerOptions {
    session_timeout: Option<Duration>,
    server: Option<HeaderValue>,
}

impl Default for ServerOptions {
    fn default() -> Self {
        Self {
            session_timeout: Some(Duration::from_secs(60)),
            server: None,
        }
    }
}

impl ServerOptions {
    /// Sets how long a session may go without a request or interleaved data
    /// from the client before it times out ([`Event::SessionTimedOut`]), or
    /// `None` for sessions to last as long as the connection. Defaults to 60
    /// seconds.
    ///
    /// Over interleaved TCP, closing the connection ends its sessions anyway,
    /// and some clients send no keepalives, so `None` is reasonable.
    ///
    /// # Panics
    ///
    /// If `timeout` is less than one second.
    pub fn session_timeout(mut self, timeout: Option<Duration>) -> Self {
        assert!(timeout.is_none_or(|t| t >= Duration::from_secs(1)));
        self.session_timeout = timeout;
        self
    }

    /// Sets the `Server` header to include in every response.
    ///
    /// # Panics
    ///
    /// If `server` isn't a valid header value.
    pub fn server(mut self, server: &str) -> Self {
        self.server = Some(HeaderValue::try_from(server).expect("valid Server header value"));
        self
    }
}

/// Identifies a session on a [`ConnectionCore`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SessionId(u64);

impl std::fmt::Display for SessionId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:016X}", self.0)
    }
}

/// A stream which has been set up within a session.
#[derive(Debug)]
pub struct SessionStream<T> {
    /// The URL from the `SETUP` request.
    pub url: Url,

    /// The interleaved channel id for RTP. RTCP uses the next one.
    pub channel: u8,

    /// The application's data, as supplied to [`ConnectionCore::respond_setup`].
    pub data: T,
}

/// A session which has ended without a `TEARDOWN`: via
/// [`Event::SessionTimedOut`] or [`ConnectionCore::into_sessions`].
#[derive(Debug)]
pub struct ClosedSession<T> {
    pub id: SessionId,
    pub streams: Vec<SessionStream<T>>,
}

/// The `RTP-Info` for one stream in a `PLAY` response; see [`ConnectionCore::respond_play`].
#[derive(Copy, Clone, Debug, Default)]
pub struct RtpInfo {
    /// The sequence number of the first packet which will be sent.
    pub seq: Option<u16>,

    /// The RTP timestamp corresponding to the start of playback.
    pub rtptime: Option<u32>,
}

/// Returned by `ConnectionCore::respond_*` when the request's session no longer
/// exists; the core has answered `454 Session Not Found`.
///
/// This can't happen today, as a session with an outstanding request
/// neither times out nor sees its `TEARDOWN` until the request is answered.
/// It's here so that allowing several outstanding requests later isn't an
/// API break.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SessionGoneError(pub SessionId);

impl std::fmt::Display for SessionGoneError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "session {} is gone", self.0)
    }
}

impl std::error::Error for SessionGoneError {}

/// An error from an RTSP server connection.
///
/// This is returned by [`ConnectionCore::poll_event`] and
/// [`ConnectionCore::read_error`]. After one, the connection should be closed.
///
/// Currently the focus is on providing detailed human-readable error messages.
/// If you wish to inspect these errors programmatically, please file an issue
/// on the `retina` repository.
#[derive(Clone, derive_more::Debug, derive_more::Display, derive_more::Error)]
#[display("{_0}")]
#[debug("{_0:?}")]
pub struct Error(#[error(not(source))] pub(crate) Arc<crate::error::ErrorInt>);

impl From<crate::error::Error> for Error {
    #[inline]
    fn from(e: crate::error::Error) -> Self {
        Self(e.0)
    }
}

struct Session<T> {
    id: SessionId,
    streams: Vec<SessionStream<T>>,
    playing: bool,

    /// When the client last kept the session alive, or `None` if it should
    /// be set from the next `poll_event`'s `now`, as after answering a
    /// request.
    last_active: Option<Instant>,
}

/// The core's record of the request it's awaiting an answer to.
struct Outstanding {
    /// Dead iff the [`Pending`] was dropped.
    liveness: Weak<()>,
    method: String,
    cseq: HeaderValue,

    /// The session this request is for, which must not time out meanwhile.
    session: Option<SessionId>,

    /// The request's span; see [`Pending::span`].
    span: tracing::Span,
}

/// The sans-I/O state of an RTSP server connection.
///
/// `T` is the application's data for each stream set up within a session.
///
/// The driver:
///
/// *   reads from the connection into [`ConnectionCore::read_buf`] while
///     [`ConnectionCore::wants_read`], calling
///     [`ConnectionCore::handle_eof`] when the client closes it;
/// *   handles events from [`ConnectionCore::poll_event`] until it returns
///     `None`, answering each [`Pending`] request (possibly later, after
///     asynchronous work) via `ConnectionCore::respond_*`, then calling
///     `poll_event` again;
/// *   writes bytes from [`ConnectionCore::transmit_buf`] to the connection,
///     between (not within) any interleaved data packets it sends, followed
///     by [`ConnectionCore::advance_transmit`];
/// *   calls [`ConnectionCore::handle_timeout`] at
///     [`ConnectionCore::poll_timeout`].
///
/// At most one [`Pending`] request is outstanding at a time, so responses go
/// out in the order requests arrived. Meanwhile the core keeps processing
/// interleaved data and session timeouts, so the driver should keep reading
/// (noticing if the client hangs up) rather than wait for the answer.
pub struct ConnectionCore<T> {
    conn_ctx: ConnectionContext,
    reader: Reader,
    eof: bool,
    options: ServerOptions,
    sessions: Vec<Session<T>>,

    /// Sessions which have timed out, to return from `poll_event`.
    timed_out: VecDeque<ClosedSession<T>>,
    transmit: TransmitBuf,
    outstanding: Option<Outstanding>,

    /// A request received while another was outstanding, to handle once it's
    /// answered. Nothing after it is decoded until then.
    held: Option<msg::Request>,
}

/// While a request is held, [`ConnectionCore::wants_read`] is false once this
/// many bytes are buffered after it.
const MAX_UNPARSED_WHILE_HELD: usize = 64 << 10;

impl<T> ConnectionCore<T> {
    pub fn new(local_addr: SocketAddr, peer_addr: SocketAddr, options: ServerOptions) -> Self {
        Self {
            conn_ctx: ConnectionContext {
                local_addr,
                peer_addr,
                established_wall: WallTime::now(),
            },
            reader: Reader::default(),
            eof: false,
            options,
            sessions: Vec::new(),
            timed_out: VecDeque::new(),
            transmit: TransmitBuf::default(),
            outstanding: None,
            held: None,
        }
    }

    /// Returns the connection's context, for logging.
    pub fn conn_ctx(&self) -> &ConnectionContext {
        &self.conn_ctx
    }

    /// Returns the buffer to read data from the client into, via
    /// [`MarkBuf::spare_capacity`] and [`MarkBuf::advance_end`].
    pub fn read_buf(&mut self) -> &mut MarkBuf {
        self.reader.buf_mut()
    }

    /// Returns true if the driver should read more from the connection.
    ///
    /// This is false only when the client has pipelined requests behind an
    /// outstanding one and a fair amount of data after those, so the buffer
    /// doesn't grow without bound.
    pub fn wants_read(&self) -> bool {
        !self.eof
            && (self.held.is_none() || self.reader.buf().unparsed_len() < MAX_UNPARSED_WHILE_HELD)
    }

    /// Notes that the client has closed its side of the connection.
    pub fn handle_eof(&mut self) {
        self.eof = true;
    }

    /// Returns an error for a failed read from the connection.
    pub fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.reader.read_error(&self.conn_ctx, source, now).into()
    }

    /// Ends the connection, returning its sessions (including any timed out
    /// but not yet returned by [`ConnectionCore::poll_event`]).
    ///
    /// Interleaved sessions can't outlive their connection, as their data
    /// flows over it. (Sessions with UDP transport, when supported, will
    /// outlive connections, so won't live in a `ConnectionCore`.)
    pub fn into_sessions(self) -> impl Iterator<Item = ClosedSession<T>> {
        self.timed_out
            .into_iter()
            .chain(self.sessions.into_iter().map(|s| ClosedSession {
                id: s.id,
                streams: s.streams,
            }))
    }

    /// Returns the sessions on this connection.
    pub fn sessions(&self) -> impl Iterator<Item = (SessionId, &[SessionStream<T>])> {
        self.sessions.iter().map(|s| (s.id, &s.streams[..]))
    }

    /// Returns the streams of the given session, if it exists.
    pub fn streams(&self, session: SessionId) -> Option<&[SessionStream<T>]> {
        self.sessions
            .iter()
            .find(|s| s.id == session)
            .map(|s| &s.streams[..])
    }

    /// Returns the streams of the given session, if it exists.
    ///
    /// This is usable at any time, including while a `PLAY` for the session
    /// is pending, e.g. to take per-stream state just before
    /// [`ConnectionCore::respond_play`].
    pub fn streams_mut(&mut self, session: SessionId) -> Option<&mut [SessionStream<T>]> {
        self.sessions
            .iter_mut()
            .find(|s| s.id == session)
            .map(|s| &mut s.streams[..])
    }

    /// Returns the bytes to write to the connection, in order.
    ///
    /// The first slice is empty iff there's nothing to write. These are
    /// suitable for vectored I/O. After writing (or copying into a buffer
    /// shared with interleaved data packets), call
    /// [`ConnectionCore::advance_transmit`]; bytes stay here until then.
    pub fn transmit_buf(&self) -> (&[u8], &[u8]) {
        self.transmit.slices()
    }

    /// Notes that the first `n` bytes of [`ConnectionCore::transmit_buf`]
    /// have been written.
    ///
    /// # Panics
    ///
    /// If `n` exceeds the bytes available.
    pub fn advance_transmit(&mut self, n: usize) {
        self.transmit.advance(n);
    }

    /// Returns when [`ConnectionCore::handle_timeout`] should next be called.
    pub fn poll_timeout(&self) -> Option<Instant> {
        let timeout = self.options.session_timeout?;
        let busy = self.outstanding.as_ref().and_then(|o| o.session);
        self.sessions
            .iter()
            .filter(|s| Some(s.id) != busy)
            .filter_map(|s| s.last_active)
            .min()
            .map(|t| t + timeout)
    }

    /// Closes sessions which have timed out; they're returned by
    /// [`ConnectionCore::poll_event`] as [`Event::SessionTimedOut`].
    ///
    /// A session with an outstanding request doesn't time out.
    pub fn handle_timeout(&mut self, now: Instant) {
        let Some(timeout) = self.options.session_timeout else {
            return;
        };
        let busy = self.outstanding.as_ref().and_then(|o| o.session);
        let mut i = 0;
        while i < self.sessions.len() {
            let s = &self.sessions[i];
            if Some(s.id) != busy && s.last_active.is_some_and(|t| t + timeout <= now) {
                let s = self.sessions.swap_remove(i);
                tracing::debug!(conn = %self.conn_ctx, session_id = %s.id, "session timed out");
                self.timed_out.push_back(ClosedSession {
                    id: s.id,
                    streams: s.streams,
                });
            } else {
                i += 1;
            }
        }
    }

    /// Returns the next event, if any.
    ///
    /// Returns an error if the client sent something unparseable, after which
    /// the connection should be closed.
    pub fn poll_event(&mut self, now: Instant) -> Option<Result<Event<T>, Error>> {
        for s in &mut self.sessions {
            s.last_active.get_or_insert(now);
        }
        loop {
            if let Some(c) = self.timed_out.pop_front() {
                return Some(Ok(Event::SessionTimedOut(c)));
            }
            if let Some(o) = &self.outstanding
                && o.liveness.strong_count() == 0
            {
                let o = self.outstanding.take().expect("outstanding is some");
                let _span = o.span.enter();
                tracing::warn!(method = %o.method, "request dropped without a response");
                self.respond(StatusCode::INTERNAL_SERVER_ERROR, Some(&o.cseq), &[], "");
                if let Some(s) = o.session.and_then(|id| self.session_mut(id)) {
                    s.last_active = Some(now);
                }
            }
            let req = if self.outstanding.is_none()
                && let Some(r) = self.held.take()
            {
                r
            } else if self.held.is_some() {
                return None;
            } else {
                let msg = match self.reader.decode(&self.conn_ctx, self.eof, now) {
                    Ok(Some(m)) => m,
                    Ok(None) => return None,
                    Err(e) => return Some(Err(e.into())),
                };
                match msg.msg {
                    msg::Message::Data(d) => {
                        // Probably RTCP receiver reports; they keep the session alive.
                        if let Some(s) = self.sessions.iter_mut().find(|s| {
                            s.streams
                                .iter()
                                .any(|st| d.channel_id.wrapping_sub(st.channel) < 2)
                        }) {
                            s.last_active = Some(now);
                        } else {
                            tracing::debug!(
                                conn = %self.conn_ctx,
                                channel_id = d.channel_id,
                                "ignoring data on unassigned channel"
                            );
                        }
                        continue;
                    }
                    msg::Message::Response(r) => {
                        tracing::debug!(
                            conn = %self.conn_ctx,
                            status = %r.status_code,
                            "ignoring unsolicited response"
                        );
                        continue;
                    }
                    msg::Message::Request(req) => req,
                }
            };
            if self.outstanding.is_some() {
                // Answer in order: after the outstanding request.
                self.held = Some(req);
                return None;
            }
            if let Some(p) = self.handle_request(req, now) {
                return Some(Ok(self.pending_event(p)));
            }
        }
    }

    /// Makes `p` the outstanding request, returning its event.
    fn pending_event(&mut self, mut p: Pending<PendingKind>) -> Event<T> {
        let session = match &p.kind {
            PendingKind::Describe => None,
            PendingKind::Setup(s) => (!s.new_session).then_some(s.session),
            PendingKind::Play(p) => Some(p.session),
            PendingKind::Teardown(t) => Some(t.session),
        };
        debug_assert!(self.outstanding.is_none());
        self.outstanding = Some(Outstanding {
            liveness: Arc::downgrade(&p.liveness),
            method: p.req.method.to_string(),
            cseq: p.cseq.clone(),
            session,
            span: p.span.clone(),
        });
        match std::mem::replace(&mut p.kind, PendingKind::Describe) {
            PendingKind::Describe => Event::Describe(p.with_kind(Describe(()))),
            PendingKind::Setup(s) => Event::Setup(p.with_kind(s)),
            PendingKind::Play(pl) => Event::Play(p.with_kind(pl)),
            PendingKind::Teardown(t) => Event::Teardown(p.with_kind(t)),
        }
    }

    /// Clears the outstanding request, which `p` must be, returning its
    /// entered span.
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request.
    fn take_outstanding<K>(&mut self, p: &Pending<K>) -> tracing::span::EnteredSpan {
        let o = self
            .outstanding
            .take_if(|o| std::ptr::eq(o.liveness.as_ptr(), Arc::as_ptr(&p.liveness)))
            .expect("Pending must be this ConnectionCore's outstanding request");
        if let Some(s) = o.session.and_then(|id| self.session_mut(id)) {
            // Set from the next `poll_event`'s `now`.
            s.last_active = None;
        }
        o.span.entered()
    }

    fn session_mut(&mut self, id: SessionId) -> Option<&mut Session<T>> {
        self.sessions.iter_mut().find(|s| s.id == id)
    }

    /// Answers a `DESCRIBE` request with the given SDP (see [`sdp`]), or
    /// rejects it.
    ///
    /// On success, the `Content-Base` is the request URL with a trailing `/`,
    /// so control URLs within the SDP are relative to it.
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request.
    pub fn respond_describe(&mut self, p: Pending<Describe>, r: Result<&str, StatusCode>) {
        let _span = self.take_outstanding(&p);
        let sdp = match r {
            Ok(sdp) => sdp,
            Err(status) => return self.respond(status, Some(&p.cseq), &[], ""),
        };
        let mut headers = vec![(HeaderName::CONTENT_TYPE, hv("application/sdp"))];
        if let Some(u) = p.url() {
            let mut base = u.as_str().to_owned();
            if !base.ends_with('/') {
                base.push('/');
            }
            headers.push((HeaderName::CONTENT_BASE, hv(&base)));
        }
        self.respond(StatusCode::OK, Some(&p.cseq), &headers, sdp);
    }

    /// Answers a `SETUP` request, or rejects it.
    ///
    /// On success, adds a stream with the given data and SSRC to the session
    /// (creating it if [`Pending::is_new_session`]), and returns the
    /// session's id, which is [`Pending::session_id`].
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request.
    pub fn respond_setup(
        &mut self,
        p: Pending<Setup>,
        r: Result<(T, u32), StatusCode>,
    ) -> Result<SessionId, SessionGoneError> {
        let _span = self.take_outstanding(&p);
        let id = p.kind.session;
        let (data, ssrc) = match r {
            Ok(r) => r,
            Err(status) => {
                self.respond(status, Some(&p.cseq), &[], "");
                return Ok(id);
            }
        };
        let i = match self.sessions.iter().position(|s| s.id == id) {
            Some(i) => i,
            None if p.kind.new_session => {
                self.sessions.push(Session {
                    id,
                    streams: Vec::new(),
                    playing: false,
                    last_active: None,
                });
                self.sessions.len() - 1
            }
            None => {
                self.respond(StatusCode::SESSION_NOT_FOUND, Some(&p.cseq), &[], "");
                return Err(SessionGoneError(id));
            }
        };
        let channel = p.kind.channel;
        self.sessions[i].streams.push(SessionStream {
            url: p.kind.url,
            channel,
            data,
        });
        let session_header = self.session_header(i);
        let transport = format!(
            "RTP/AVP/TCP;unicast;interleaved={}-{};ssrc={ssrc:08X}",
            channel,
            channel + 1
        );
        self.respond(
            StatusCode::OK,
            Some(&p.cseq),
            &[session_header, (HeaderName::TRANSPORT, hv(&transport))],
            "",
        );
        Ok(id)
    }

    /// Answers a `PLAY` request with `rtp_info` for each of the session's
    /// streams (see [`ConnectionCore::streams`]), or rejects it.
    ///
    /// On success, the driver should write the response (from
    /// [`ConnectionCore::transmit_buf`]) before any of the session's packets.
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request, or if `rtp_info` doesn't
    /// have one entry per stream.
    pub fn respond_play(
        &mut self,
        p: Pending<Play>,
        r: Result<&[RtpInfo], StatusCode>,
    ) -> Result<(), SessionGoneError> {
        let _span = self.take_outstanding(&p);
        let rtp_info = match r {
            Ok(r) => r,
            Err(status) => {
                self.respond(status, Some(&p.cseq), &[], "");
                return Ok(());
            }
        };
        let id = p.kind.session;
        let Some(i) = self.sessions.iter().position(|s| s.id == id) else {
            self.respond(StatusCode::SESSION_NOT_FOUND, Some(&p.cseq), &[], "");
            return Err(SessionGoneError(id));
        };
        let session = &mut self.sessions[i];
        assert_eq!(rtp_info.len(), session.streams.len());
        session.playing = true;
        let mut info = String::new();
        for (s, r) in session.streams.iter().zip(rtp_info) {
            if !info.is_empty() {
                info.push(',');
            }
            write!(&mut info, "url={}", s.url).unwrap();
            if let Some(seq) = r.seq {
                write!(&mut info, ";seq={seq}").unwrap();
            }
            if let Some(t) = r.rtptime {
                write!(&mut info, ";rtptime={t}").unwrap();
            }
        }
        let headers = [
            self.session_header(i),
            (HeaderName::RANGE, hv("npt=now-")),
            (HeaderName::RTP_INFO, hv(&info)),
        ];
        self.respond(StatusCode::OK, Some(&p.cseq), &headers, "");
        Ok(())
    }

    /// Answers a `TEARDOWN` request, ending the session and returning its
    /// streams.
    ///
    /// The whole session ends, even if the request named one of its streams.
    /// The driver should stop sending the session's streams before writing
    /// the response (from [`ConnectionCore::transmit_buf`]), as the client
    /// may reuse their interleaved channels in a later `SETUP`.
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request.
    pub fn respond_teardown(
        &mut self,
        p: Pending<Teardown>,
    ) -> Result<Vec<SessionStream<T>>, SessionGoneError> {
        let _span = self.take_outstanding(&p);
        let id = p.kind.session;
        let Some(i) = self.sessions.iter().position(|s| s.id == id) else {
            self.respond(StatusCode::SESSION_NOT_FOUND, Some(&p.cseq), &[], "");
            return Err(SessionGoneError(id));
        };
        let s = self.sessions.swap_remove(i);
        self.respond(StatusCode::OK, Some(&p.cseq), &[], "");
        Ok(s.streams)
    }

    /// Rejects any kind of request with the given status and extra headers,
    /// e.g. `401 Unauthorized` with `WWW-Authenticate`.
    ///
    /// # Panics
    ///
    /// If `p` isn't this core's outstanding request.
    pub fn reject<K>(
        &mut self,
        p: Pending<K>,
        status: StatusCode,
        headers: &[(HeaderName, HeaderValue)],
    ) {
        let _span = self.take_outstanding(&p);
        self.respond(status, Some(&p.cseq), headers, "");
    }

    /// Handles a request, returning it if it needs the application's answer.
    fn handle_request(&mut self, req: msg::Request, now: Instant) -> Option<Pending<PendingKind>> {
        let span = tracing::info_span!(
            "rtsp_request",
            method = %req.method,
            url = req.request_uri.as_ref().map(Url::as_str),
            conn = %self.conn_ctx,
        );
        let _enter = span.enter();
        tracing::trace!("request:\n{req}");
        let Some(cseq_value) = req.headers.get("CSeq").cloned() else {
            self.respond(StatusCode::BAD_REQUEST, None, &[], "");
            return None;
        };
        let cseq = Some(&cseq_value);
        if let Some(r) = req.headers.get("Require") {
            let r = r.clone();
            self.respond(
                StatusCode::OPTION_NOT_SUPPORTED,
                cseq,
                &[(HeaderName::UNSUPPORTED, r)],
                "",
            );
            return None;
        }
        let session_i = match req.headers.get("Session") {
            None => None,
            Some(v) => {
                let id = v.split(';').next().unwrap_or("").trim();
                match self
                    .sessions
                    .iter()
                    .position(|s| s.id.to_string().eq_ignore_ascii_case(id))
                {
                    Some(i) => {
                        self.sessions[i].last_active = Some(now);
                        Some(i)
                    }
                    None => {
                        self.respond(StatusCode::SESSION_NOT_FOUND, cseq, &[], "");
                        return None;
                    }
                }
            }
        };
        let method: &str = &req.method;
        let kind = match method {
            "OPTIONS" => {
                self.respond(
                    StatusCode::OK,
                    cseq,
                    &[(
                        HeaderName::PUBLIC,
                        hv("OPTIONS, DESCRIBE, SETUP, PLAY, TEARDOWN, GET_PARAMETER, SET_PARAMETER"),
                    )],
                    "",
                );
                return None;
            }
            "GET_PARAMETER" | "SET_PARAMETER" => {
                let headers = session_i
                    .map(|i| self.session_header(i))
                    .into_iter()
                    .collect::<Vec<_>>();
                self.respond(StatusCode::OK, cseq, &headers, "");
                return None;
            }
            "DESCRIBE" => PendingKind::Describe,
            "SETUP" => {
                let Some(url) = req.request_uri.clone() else {
                    self.respond(StatusCode::BAD_REQUEST, cseq, &[], "");
                    return None;
                };
                if let Some(i) = session_i
                    && self.sessions[i].playing
                {
                    self.respond(StatusCode::METHOD_NOT_VALID_IN_THIS_STATE, cseq, &[], "");
                    return None;
                }
                let Some(channel) = req
                    .headers
                    .get("Transport")
                    .and_then(|t| self.choose_channel(t))
                else {
                    self.respond(StatusCode::UNSUPPORTED_TRANSPORT, cseq, &[], "");
                    return None;
                };
                let (session, new_session) = match session_i {
                    Some(i) => (self.sessions[i].id, false),
                    None => (self.new_session_id(), true),
                };
                PendingKind::Setup(Setup {
                    session,
                    new_session,
                    url,
                    channel,
                })
            }
            "PLAY" => {
                let Some(i) = session_i else {
                    self.respond(StatusCode::SESSION_NOT_FOUND, cseq, &[], "");
                    return None;
                };
                if self.sessions[i].playing {
                    // Live streams can't seek, so there's nothing to do.
                    let h = self.session_header(i);
                    self.respond(StatusCode::OK, cseq, &[h], "");
                    return None;
                }
                PendingKind::Play(Play {
                    session: self.sessions[i].id,
                })
            }
            "TEARDOWN" => {
                let Some(i) = session_i else {
                    self.respond(StatusCode::SESSION_NOT_FOUND, cseq, &[], "");
                    return None;
                };
                PendingKind::Teardown(Teardown {
                    session: self.sessions[i].id,
                })
            }
            _ => {
                self.respond(StatusCode::NOT_IMPLEMENTED, cseq, &[], "");
                return None;
            }
        };
        Some(Pending {
            req,
            cseq: cseq_value,
            kind,
            liveness: Arc::new(()),
            span: span.clone(),
        })
    }

    fn new_session_id(&self) -> SessionId {
        loop {
            let id = SessionId(rand::random());
            if !self.sessions.iter().any(|s| s.id == id) {
                return id;
            }
        }
    }

    /// Chooses an interleaved RTP channel id per a `Transport` request header,
    /// or returns `None` if no transport it lists is supported.
    fn choose_channel(&self, transport: &str) -> Option<u8> {
        let in_use = |c: u8| {
            self.sessions.iter().any(|s| {
                s.streams
                    .iter()
                    .any(|st| c.wrapping_sub(st.channel) < 2 || st.channel.wrapping_sub(c) < 2)
            })
        };
        for spec in transport.split(',') {
            let mut params = spec.split(';').map(str::trim);
            let protocol = params.next().unwrap_or("");
            if !protocol.eq_ignore_ascii_case("RTP/AVP/TCP") {
                continue;
            }
            let mut requested = None;
            let mut multicast = false;
            for p in params {
                if let Some(v) = p.strip_prefix("interleaved=") {
                    let first = v.split('-').next().unwrap_or("");
                    requested = u8::from_str_radix(first, 10).ok();
                } else if p.eq_ignore_ascii_case("multicast") {
                    multicast = true;
                }
            }
            if multicast {
                continue;
            }
            if let Some(c) = requested
                && c < 255
                && !in_use(c)
            {
                return Some(c);
            }
            return (0..=254).step_by(2).find(|&c| !in_use(c));
        }
        None
    }

    fn session_header(&self, i: usize) -> (HeaderName, HeaderValue) {
        let id = self.sessions[i].id;
        // Without `timeout`, clients assume 60 seconds (RFC 2326 section
        // 12.37), so keepalives continue harmlessly when timeouts are off.
        let value = match self.options.session_timeout {
            Some(t) => format!("{id};timeout={}", t.as_secs()),
            None => id.to_string(),
        };
        (HeaderName::SESSION, hv(&value))
    }

    fn respond(
        &mut self,
        status: StatusCode,
        cseq: Option<&HeaderValue>,
        headers: &[(HeaderName, HeaderValue)],
        body: &str,
    ) {
        let mut h = msg::Headers::default();
        if let Some(c) = cseq {
            h.insert(HeaderName::CSEQ, c.clone());
        }
        if let Some(s) = &self.options.server {
            h.insert(HeaderName::SERVER, s.clone());
        }
        for (name, value) in headers {
            h.insert(name.clone(), value.clone());
        }
        if !body.is_empty() {
            h.insert(HeaderName::CONTENT_LENGTH, hv(&body.len().to_string()));
        }
        let resp = msg::Response {
            status_code: status,
            reason_phrase: status.canonical_reason().to_owned(),
            headers: h,
        };
        tracing::trace!("response:\n{resp}{body}");
        resp.write_head(&mut self.transmit)
            .expect("TransmitBuf writes are infallible");
        self.transmit
            .write_all(body.as_bytes())
            .expect("TransmitBuf writes are infallible");
    }
}

fn hv(s: &str) -> HeaderValue {
    HeaderValue::try_from(s).expect("valid header value")
}

/// An event from [`ConnectionCore::poll_event`].
#[non_exhaustive]
pub enum Event<T> {
    Describe(Pending<Describe>),
    Setup(Pending<Setup>),
    Play(Pending<Play>),

    Teardown(Pending<Teardown>),

    /// A session timed out; the driver should stop sending its streams.
    SessionTimedOut(ClosedSession<T>),
}

/// A request awaiting the application's answer via the matching
/// `ConnectionCore::respond_*` method.
///
/// This is owned, so the application may answer after asynchronous work
/// (e.g. waiting for codec parameters, or an authentication lookup) while the
/// driver keeps polling the core. If dropped unanswered, the core responds
/// `500 Internal Server Error` at the next [`ConnectionCore::poll_event`].
#[must_use = "answer via ConnectionCore::respond_*; dropping sends a 500"]
pub struct Pending<K> {
    req: msg::Request,
    cseq: HeaderValue,
    kind: K,

    /// The core holds a `Weak` to this, to notice if it's dropped.
    liveness: Arc<()>,

    span: tracing::Span,
}

impl<K> Pending<K> {
    pub fn request(&self) -> &msg::Request {
        &self.req
    }

    /// Returns a span for this request, with the method, URL, and connection.
    ///
    /// The core enters it while handling the request and its answer. The
    /// application may too, e.g. via [`tracing::Instrument`] on asynchronous
    /// work toward the answer. It lasts only as long as the request.
    pub fn span(&self) -> &tracing::Span {
        &self.span
    }

    fn with_kind<K2>(self, kind: K2) -> Pending<K2> {
        Pending {
            req: self.req,
            cseq: self.cseq,
            kind,
            liveness: self.liveness,
            span: self.span,
        }
    }
}

impl<K> std::fmt::Debug for Pending<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Pending")
            .field("method", &&*self.req.method)
            .field("cseq", &self.cseq)
            .finish_non_exhaustive()
    }
}

enum PendingKind {
    Describe,
    Setup(Setup),
    Play(Play),
    Teardown(Teardown),
}

/// A `DESCRIBE` request, answered via [`ConnectionCore::respond_describe`].
#[derive(Debug)]
pub struct Describe(());

impl Pending<Describe> {
    pub fn url(&self) -> Option<&Url> {
        self.req.request_uri.as_ref()
    }
}

/// A `SETUP` request for an RTP/AVP/TCP stream, answered via
/// [`ConnectionCore::respond_setup`].
#[derive(Debug)]
pub struct Setup {
    session: SessionId,
    new_session: bool,
    url: Url,
    channel: u8,
}

impl Pending<Setup> {
    pub fn url(&self) -> &Url {
        &self.kind.url
    }

    /// Returns the session this stream will be added to if accepted: an
    /// existing one (aggregate `SETUP`), or one created on acceptance.
    pub fn session_id(&self) -> SessionId {
        self.kind.session
    }

    /// Returns true if accepting will create the session.
    pub fn is_new_session(&self) -> bool {
        self.kind.new_session
    }

    /// Returns the interleaved channel id RTP will use; RTCP uses the next.
    pub fn channel(&self) -> u8 {
        self.kind.channel
    }
}

/// A `PLAY` request for a session which isn't already playing, answered via
/// [`ConnectionCore::respond_play`].
#[derive(Debug)]
pub struct Play {
    session: SessionId,
}

impl Pending<Play> {
    pub fn session_id(&self) -> SessionId {
        self.kind.session
    }
}

/// A `TEARDOWN` request, answered via [`ConnectionCore::respond_teardown`].
///
/// Until then, the session stays (with its interleaved channels allocated),
/// so the application can make sure it has stopped sending the session's
/// streams before the response goes out.
#[derive(Debug)]
pub struct Teardown {
    session: SessionId,
}

impl Pending<Teardown> {
    pub fn url(&self) -> Option<&Url> {
        self.req.request_uri.as_ref()
    }

    pub fn session_id(&self) -> SessionId {
        self.kind.session
    }
}

/// A media description for [`sdp`], created via [`SdpMedia::new`].
///
/// This is `#[non_exhaustive]`, so that fields can be added without breaking
/// callers, including fields which exist only with some features, which
/// Cargo's feature unification may enable.
#[non_exhaustive]
pub struct SdpMedia<'a> {
    pub format: &'a crate::codec::PayloadFormat,
    pub payload_type: u8,

    /// The control URL, relative to the `DESCRIBE` response's `Content-Base`.
    pub control: &'a str,

    /// The RTP header extensions sent, described via `a=extmap` attributes.
    /// These should match [`crate::rtp::SenderOptions::extension_ids`].
    #[cfg(feature = "unstable-extensions")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-extensions")))]
    pub extension_ids: crate::rtp::ExtensionIds,
    #[cfg(not(feature = "unstable-extensions"))]
    pub(crate) extension_ids: crate::rtp::ExtensionIds,
}

impl<'a> SdpMedia<'a> {
    /// Returns a media description with the given format, payload type, and
    /// control URL, which is relative to the `DESCRIBE` response's
    /// `Content-Base`.
    #[inline]
    pub fn new(
        format: &'a crate::codec::PayloadFormat,
        payload_type: u8,
        control: &'a str,
    ) -> Self {
        Self {
            format,
            payload_type,
            control,
            extension_ids: crate::rtp::ExtensionIds::default(),
        }
    }

    pub_if_unstable_extensions! {
        /// Returns `self` with the given RTP header extensions; see
        /// [`SdpMedia::extension_ids`].
        #[inline]
        pub fn with_extension_ids(self, extension_ids: crate::rtp::ExtensionIds) -> Self {
            Self {
                extension_ids,
                ..self
            }
        }
    }
}

/// Returns an SDP presentation description for a `DESCRIBE` response, with
/// aggregate control.
pub fn sdp(session_name: &str, media: &[SdpMedia<'_>]) -> String {
    let mut out = format!(
        "v=0\r\n\
         o=- 0 0 IN IP4 0.0.0.0\r\n\
         s={session_name}\r\n\
         c=IN IP4 0.0.0.0\r\n\
         t=0 0\r\n\
         a=control:*\r\n\
         a=range:npt=now-\r\n"
    );
    for m in media {
        let f = m.format;
        let pt = m.payload_type;
        write!(
            &mut out,
            "m={} 0 RTP/AVP {pt}\r\na=rtpmap:{pt} {}/{}",
            f.media(),
            f.encoding_name(),
            f.clock_rate()
        )
        .unwrap();
        if let Some(c) = f.channels() {
            write!(&mut out, "/{c}").unwrap();
        }
        out.push_str("\r\n");
        if let Some(fmtp) = f.fmtp() {
            write!(&mut out, "a=fmtp:{pt} {fmtp}\r\n").unwrap();
        }
        write!(&mut out, "a=control:{}\r\n", m.control).unwrap();
        for (id, uri) in m.extension_ids.sdp_extmap() {
            write!(&mut out, "a=extmap:{id} {uri}\r\n").unwrap();
        }
    }
    out
}

#[cfg(test)]
mod tests;
