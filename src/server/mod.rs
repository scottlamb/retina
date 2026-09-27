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
//! This API is a prototype and likely to change.

use std::collections::VecDeque;
use std::fmt::Write as _;
use std::net::SocketAddr;
use std::time::{Duration, Instant};

use url::Url;

use crate::buf::MarkBuf;
use crate::rtsp::msg::{self, HeaderName, HeaderValue, StatusCode};
use crate::rtsp::reader::Reader;
use crate::{ConnectionContext, Error, WallTime};

/// Options for a [`ConnectionCore`].
#[derive(Clone, Debug)]
pub struct ServerOptions {
    session_timeout: Duration,
    server: Option<HeaderValue>,
}

impl Default for ServerOptions {
    fn default() -> Self {
        Self {
            session_timeout: Duration::from_secs(60),
            server: None,
        }
    }
}

impl ServerOptions {
    /// Sets how long a session may go without a request or interleaved data
    /// from the client before it's closed. Defaults to 60 seconds.
    ///
    /// # Panics
    ///
    /// If `timeout` is less than one second.
    pub fn session_timeout(mut self, timeout: Duration) -> Self {
        assert!(timeout >= Duration::from_secs(1));
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

    /// The application's data, as supplied to [`SetupRequest::accept`].
    pub data: T,
}

/// Why a session was closed.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CloseReason {
    /// The client sent `TEARDOWN`.
    Teardown,

    /// The client didn't keep the session alive.
    Timeout,
}

/// A session which has been closed, returned via [`Event::SessionClosed`].
#[derive(Debug)]
pub struct ClosedSession<T> {
    pub id: SessionId,
    pub reason: CloseReason,
    pub streams: Vec<SessionStream<T>>,
}

/// The `RTP-Info` for one stream in a `PLAY` response; see [`PlayRequest::respond`].
#[derive(Copy, Clone, Debug, Default)]
pub struct RtpInfo {
    /// The sequence number of the first packet which will be sent.
    pub seq: Option<u16>,

    /// The RTP timestamp corresponding to the start of playback.
    pub rtptime: Option<u32>,
}

struct Session<T> {
    id: SessionId,
    streams: Vec<SessionStream<T>>,
    playing: bool,
    deadline: Instant,
}

/// The sans-I/O state of an RTSP server connection.
///
/// `T` is the application's data for each stream set up within a session.
///
/// The driver:
///
/// *   reads from the connection into [`ConnectionCore::read_buf`], calling
///     [`ConnectionCore::handle_eof`] when the client closes it;
/// *   handles events from [`ConnectionCore::poll_event`] until it returns
///     `None`;
/// *   writes bytes from [`ConnectionCore::poll_transmit`] to the connection,
///     between (not within) any interleaved data packets it sends;
/// *   calls [`ConnectionCore::handle_timeout`] at
///     [`ConnectionCore::poll_timeout`].
pub struct ConnectionCore<T> {
    conn_ctx: ConnectionContext,
    reader: Reader,
    eof: bool,
    options: ServerOptions,
    sessions: Vec<Session<T>>,
    closed: VecDeque<ClosedSession<T>>,
    transmit: Vec<u8>,
}

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
            closed: VecDeque::new(),
            transmit: Vec::new(),
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

    /// Notes that the client has closed its side of the connection.
    pub fn handle_eof(&mut self) {
        self.eof = true;
    }

    /// Returns an error for a failed read from the connection.
    pub fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.reader.read_error(&self.conn_ctx, source, now)
    }

    /// Returns the sessions on this connection.
    pub fn sessions(&self) -> impl Iterator<Item = (SessionId, &[SessionStream<T>])> {
        self.sessions.iter().map(|s| (s.id, &s.streams[..]))
    }

    /// Returns bytes to write to the connection, if any.
    ///
    /// Each call returns new bytes; the caller should write them all before
    /// the next call.
    pub fn poll_transmit(&mut self) -> Option<Vec<u8>> {
        if self.transmit.is_empty() {
            return None;
        }
        Some(std::mem::take(&mut self.transmit))
    }

    /// Returns when [`ConnectionCore::handle_timeout`] should next be called.
    pub fn poll_timeout(&self) -> Option<Instant> {
        self.sessions.iter().map(|s| s.deadline).min()
    }

    /// Closes sessions which have timed out; they're returned by
    /// [`ConnectionCore::poll_event`].
    pub fn handle_timeout(&mut self, now: Instant) {
        let mut i = 0;
        while i < self.sessions.len() {
            if self.sessions[i].deadline <= now {
                let s = self.sessions.swap_remove(i);
                log::debug!("{}: session {} timed out", self.conn_ctx, s.id);
                self.closed.push_back(ClosedSession {
                    id: s.id,
                    reason: CloseReason::Timeout,
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
    pub fn poll_event(&mut self, now: Instant) -> Option<Result<Event<'_, T>, Error>> {
        let pending = loop {
            if let Some(c) = self.closed.pop_front() {
                return Some(Ok(Event::SessionClosed(c)));
            }
            let msg = match self.reader.decode(&self.conn_ctx, self.eof, now) {
                Ok(Some(m)) => m,
                Ok(None) => return None,
                Err(e) => return Some(Err(e)),
            };
            match msg.msg {
                msg::Message::Data(d) => {
                    // Probably RTCP receiver reports; they keep the session alive.
                    let timeout = self.options.session_timeout;
                    if let Some(s) = self.sessions.iter_mut().find(|s| {
                        s.streams
                            .iter()
                            .any(|st| d.channel_id.wrapping_sub(st.channel) < 2)
                    }) {
                        s.deadline = now + timeout;
                    } else {
                        log::debug!(
                            "{}: ignoring data on unassigned channel {}",
                            self.conn_ctx,
                            d.channel_id
                        );
                    }
                }
                msg::Message::Response(r) => {
                    log::debug!(
                        "{}: ignoring unsolicited response {}",
                        self.conn_ctx,
                        r.status_code
                    );
                }
                msg::Message::Request(req) => {
                    if let Some(p) = self.handle_request(req, now) {
                        break p;
                    }
                }
            }
        };
        let base = PendingRequest {
            core: self,
            req: pending.req,
            cseq: pending.cseq,
            now,
            responded: false,
        };
        Some(Ok(match pending.kind {
            PendingKind::Describe => Event::Describe(DescribeRequest(base)),
            PendingKind::Setup {
                session_i,
                url,
                channel,
            } => Event::Setup(SetupRequest {
                base,
                session_i,
                url,
                channel,
            }),
            PendingKind::Play { session_i } => Event::Play(PlayRequest { base, session_i }),
        }))
    }

    /// Handles a request, returning it if it needs the application's answer.
    fn handle_request(&mut self, req: msg::Request, now: Instant) -> Option<Pending> {
        log::trace!("{}: request:\n{req}", self.conn_ctx);
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
                        self.sessions[i].deadline = now + self.options.session_timeout;
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
                PendingKind::Setup {
                    session_i,
                    url,
                    channel,
                }
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
                PendingKind::Play { session_i: i }
            }
            "TEARDOWN" => {
                let Some(i) = session_i else {
                    self.respond(StatusCode::SESSION_NOT_FOUND, cseq, &[], "");
                    return None;
                };
                let s = self.sessions.swap_remove(i);
                self.closed.push_back(ClosedSession {
                    id: s.id,
                    reason: CloseReason::Teardown,
                    streams: s.streams,
                });
                self.respond(StatusCode::OK, cseq, &[], "");
                return None;
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
        })
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
        let s = &self.sessions[i];
        (
            HeaderName::SESSION,
            hv(&format!(
                "{};timeout={}",
                s.id,
                self.options.session_timeout.as_secs()
            )),
        )
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
        log::trace!("{}: response:\n{resp}{body}", self.conn_ctx);
        resp.write_head(&mut self.transmit)
            .expect("Vec writes are infallible");
        self.transmit.extend_from_slice(body.as_bytes());
    }
}

fn hv(s: &str) -> HeaderValue {
    HeaderValue::try_from(s).expect("valid header value")
}

/// A request awaiting the application's answer, in owned form.
struct Pending {
    req: msg::Request,
    cseq: HeaderValue,
    kind: PendingKind,
}

enum PendingKind {
    Describe,
    Setup {
        session_i: Option<usize>,
        url: Url,
        channel: u8,
    },
    Play {
        session_i: usize,
    },
}

/// An event from [`ConnectionCore::poll_event`].
#[non_exhaustive]
pub enum Event<'a, T> {
    Describe(DescribeRequest<'a, T>),
    Setup(SetupRequest<'a, T>),
    Play(PlayRequest<'a, T>),

    /// A session was closed; the driver should stop sending its streams.
    SessionClosed(ClosedSession<T>),
}

/// A request awaiting a response. If dropped without one, responds with
/// `500 Internal Server Error`.
struct PendingRequest<'a, T> {
    core: &'a mut ConnectionCore<T>,
    req: msg::Request,
    cseq: HeaderValue,

    /// The time passed to the `poll_event` which returned this request.
    now: Instant,
    responded: bool,
}

impl<T> PendingRequest<'_, T> {
    fn respond(&mut self, status: StatusCode, headers: &[(HeaderName, HeaderValue)], body: &str) {
        debug_assert!(!self.responded);
        self.responded = true;
        self.core.respond(status, Some(&self.cseq), headers, body);
    }
}

impl<T> Drop for PendingRequest<'_, T> {
    fn drop(&mut self) {
        if !self.responded {
            log::warn!(
                "{}: {} request dropped without a response",
                self.core.conn_ctx,
                &*self.req.method
            );
            self.respond(StatusCode::INTERNAL_SERVER_ERROR, &[], "");
        }
    }
}

/// A `DESCRIBE` request, which the application answers with SDP; see [`sdp`].
pub struct DescribeRequest<'a, T>(PendingRequest<'a, T>);

impl<T> DescribeRequest<'_, T> {
    pub fn request(&self) -> &msg::Request {
        &self.0.req
    }

    pub fn url(&self) -> Option<&Url> {
        self.0.req.request_uri.as_ref()
    }

    /// Responds with the given SDP.
    ///
    /// The `Content-Base` is the request URL with a trailing `/`, so control
    /// URLs within the SDP are relative to it.
    pub fn respond(mut self, sdp: &str) {
        let mut headers = vec![(HeaderName::CONTENT_TYPE, hv("application/sdp"))];
        if let Some(u) = self.url() {
            let mut base = u.as_str().to_owned();
            if !base.ends_with('/') {
                base.push('/');
            }
            headers.push((HeaderName::CONTENT_BASE, hv(&base)));
        }
        self.0.respond(StatusCode::OK, &headers, sdp);
    }

    pub fn reject(mut self, status: StatusCode) {
        self.0.respond(status, &[], "");
    }
}

/// A `SETUP` request for an RTP/AVP/TCP stream.
pub struct SetupRequest<'a, T> {
    base: PendingRequest<'a, T>,
    session_i: Option<usize>,
    url: Url,
    channel: u8,
}

impl<T> SetupRequest<'_, T> {
    pub fn request(&self) -> &msg::Request {
        &self.base.req
    }

    pub fn url(&self) -> &Url {
        &self.url
    }

    /// Returns the existing session this stream is being added to, if any.
    pub fn session(&self) -> Option<SessionId> {
        self.session_i.map(|i| self.base.core.sessions[i].id)
    }

    /// Returns the interleaved channel id RTP will use; RTCP uses the next.
    pub fn channel(&self) -> u8 {
        self.channel
    }

    /// Accepts the request, adding a stream with the given data and SSRC to
    /// the session (creating one if needed). Returns the session's id.
    pub fn accept(mut self, data: T, ssrc: u32) -> SessionId {
        let now = self.base.now;
        let core = &mut *self.base.core;
        let i = match self.session_i {
            Some(i) => i,
            None => {
                let mut id;
                loop {
                    id = SessionId(rand::random());
                    if !core.sessions.iter().any(|s| s.id == id) {
                        break;
                    }
                }
                core.sessions.push(Session {
                    id,
                    streams: Vec::new(),
                    playing: false,
                    deadline: now + core.options.session_timeout,
                });
                core.sessions.len() - 1
            }
        };
        let session = &mut core.sessions[i];
        session.streams.push(SessionStream {
            url: self.url.clone(),
            channel: self.channel,
            data,
        });
        let id = session.id;
        let session_header = core.session_header(i);
        let transport = format!(
            "RTP/AVP/TCP;unicast;interleaved={}-{};ssrc={ssrc:08X}",
            self.channel,
            self.channel + 1
        );
        self.base.respond(
            StatusCode::OK,
            &[session_header, (HeaderName::TRANSPORT, hv(&transport))],
            "",
        );
        id
    }

    pub fn reject(mut self, status: StatusCode) {
        self.base.respond(status, &[], "");
    }
}

/// A `PLAY` request for a session which isn't already playing.
pub struct PlayRequest<'a, T> {
    base: PendingRequest<'a, T>,
    session_i: usize,
}

impl<T> PlayRequest<'_, T> {
    pub fn request(&self) -> &msg::Request {
        &self.base.req
    }

    pub fn session(&self) -> SessionId {
        self.base.core.sessions[self.session_i].id
    }

    pub fn streams(&self) -> &[SessionStream<T>] {
        &self.base.core.sessions[self.session_i].streams
    }

    pub fn streams_mut(&mut self) -> &mut [SessionStream<T>] {
        &mut self.base.core.sessions[self.session_i].streams
    }

    /// Responds successfully, with `rtp_info` for each of [`PlayRequest::streams`].
    ///
    /// The driver should write the response (from
    /// [`ConnectionCore::poll_transmit`]) before any of the session's packets.
    ///
    /// # Panics
    ///
    /// If `rtp_info` doesn't have one entry per stream.
    pub fn respond(mut self, rtp_info: &[RtpInfo]) {
        let core = &mut *self.base.core;
        let session = &mut core.sessions[self.session_i];
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
            core.session_header(self.session_i),
            (HeaderName::RANGE, hv("npt=now-")),
            (HeaderName::RTP_INFO, hv(&info)),
        ];
        self.base.respond(StatusCode::OK, &headers, "");
    }

    pub fn reject(mut self, status: StatusCode) {
        self.base.respond(status, &[], "");
    }
}

/// A media description for [`sdp`].
pub struct SdpMedia<'a> {
    pub format: &'a crate::codec::PayloadFormat,
    pub payload_type: u8,

    /// The control URL, relative to the `DESCRIBE` response's `Content-Base`.
    pub control: &'a str,
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
    }
    out
}

#[cfg(test)]
mod tests;
