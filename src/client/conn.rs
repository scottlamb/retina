// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sans-I/O request/response handling for an RTSP client connection; see
//! [`ConnCore`].

use std::time::Instant;

use bytes::Bytes;
use log::debug;

use super::channel_mapping::ChannelMappings;
use super::{SessionOptions, Tool, parse};
use crate::buf::MarkBuf;
use crate::rtsp::msg::{self, OwnedMessage, StatusCode};
use crate::rtsp::reader::Reader;
use crate::rtsp::transmit::TransmitBuf;
use crate::{ConnectionContext, Error, ErrorInt, RtspMessageContext};

/// How [`ConnCore::poll_response`] treats messages other than the response
/// it's waiting for.
#[derive(Copy, Clone, Debug)]
pub(crate) enum ResponseMode {
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

/// A request awaiting its response.
struct Pending {
    req: OwnedMessage,
    cseq: u32,
    mode: ResponseMode,
}

/// A successful response from [`ConnCore::poll_response`].
pub(crate) struct Response {
    pub(crate) msg_ctx: RtspMessageContext,
    pub(crate) cseq: u32,
    pub(crate) method: msg::Method,
    pub(crate) head: msg::Response,
    pub(crate) body: Bytes,
}

impl Response {
    /// Returns an error about this response.
    pub(crate) fn error(&self, conn_ctx: &ConnectionContext, description: String) -> Error {
        wrap!(ErrorInt::RtspResponseError {
            conn_ctx: *conn_ctx,
            msg_ctx: self.msg_ctx,
            method: self.method.clone(),
            cseq: self.cseq,
            status: self.head.status_code,
            description,
        })
    }
}

/// The state of an RTSP client connection: its parser and read buffer,
/// outgoing bytes, `CSeq` numbering, authentication, and interleaved channel
/// assignments.
///
/// This sends one request at a time via [`ConnCore::send`] and matches up its
/// response in [`ConnCore::poll_response`], retrying once with Digest
/// authentication if the server asks for it. It's shared by the pre-`PLAY`
/// [`super::SessionCore`], the [`super::PlayingCore`] (which sends its own
/// keepalives via [`ConnCore::queue`]), and background `TEARDOWN`s.
pub(crate) struct ConnCore {
    pub(crate) ctx: ConnectionContext,
    pub(crate) reader: Reader,

    /// True if the peer has closed the connection.
    pub(crate) eof: bool,

    pub(crate) options: SessionOptions,
    pub(crate) requested_auth: Option<http_auth::PasswordClient>,
    pub(crate) tool: Option<Tool>,

    /// The next `CSeq` header value to use when sending an RTSP request.
    next_cseq: u32,

    pub(crate) channels: ChannelMappings,

    /// True if data has been received on an unassigned interleaved channel.
    pub(crate) seen_unassigned: bool,

    /// Bytes not yet written; see [`ConnCore::transmit_buf`].
    pub(crate) transmit: TransmitBuf,

    pending: Option<Pending>,
}

impl ConnCore {
    pub(crate) fn new(ctx: ConnectionContext, options: SessionOptions) -> Self {
        Self {
            ctx,
            reader: Reader::new(options.get_max_message_size()),
            eof: false,
            options,
            requested_auth: None,
            tool: None,
            next_cseq: 1,
            channels: ChannelMappings::default(),
            seen_unassigned: false,
            transmit: TransmitBuf::default(),
            pending: None,
        }
    }

    /// Starts over on a fresh connection, keeping the options, authentication,
    /// and tool.
    pub(crate) fn reconnect(&mut self, ctx: ConnectionContext) {
        let options = std::mem::take(&mut self.options);
        let requested_auth = self.requested_auth.take();
        let tool = self.tool.take();
        *self = Self {
            requested_auth,
            tool,
            ..Self::new(ctx, options)
        };
    }

    #[inline]
    pub(crate) fn read_buf(&mut self) -> &mut MarkBuf {
        self.reader.buf_mut()
    }

    pub(crate) fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.reader.read_error(&self.ctx, source, now)
    }

    /// Returns true iff a request is awaiting its response.
    pub(crate) fn has_pending(&self) -> bool {
        self.pending.is_some()
    }

    /// Fills out `req` with authorization, `CSeq`, and `User-Agent` headers,
    /// returning the `CSeq`.
    pub(crate) fn fill_req(&mut self, req: &mut OwnedMessage) -> Result<u32, Error> {
        super::fill_req(
            &mut self.next_cseq,
            &self.options,
            &mut self.requested_auth,
            req,
        )
    }

    /// Appends a message to the bytes for [`ConnCore::transmit_buf`].
    pub(crate) fn queue(&mut self, msg: &OwnedMessage) {
        msg.write(&mut self.transmit)
            .expect("TransmitBuf Writer is infallible");
    }

    /// Appends an interleaved data message on channel `channel_id`, with a
    /// body of `data` concatenated, to the bytes for
    /// [`ConnCore::transmit_buf`].
    ///
    /// The caller has checked that the body fits in 65,535 bytes.
    #[cfg(feature = "unstable-send")]
    pub(crate) fn queue_data(&mut self, channel_id: u8, data: &[&[u8]]) {
        use std::io::Write as _;
        let body_len = data.iter().map(|d| d.len()).sum::<usize>();
        let body_len = u16::try_from(body_len).expect("caller checked body length");
        crate::rtsp::msg::Data {
            channel_id,
            body_len,
        }
        .write(&mut self.transmit)
        .expect("TransmitBuf Writer is infallible");
        for d in data {
            self.transmit
                .write_all(d)
                .expect("TransmitBuf Writer is infallible");
        }
    }

    /// Sends `req`, expecting its response from [`ConnCore::poll_response`].
    pub(crate) fn send(&mut self, mode: ResponseMode, mut req: OwnedMessage) -> Result<(), Error> {
        if let Some(p) = &self.pending {
            bail!(ErrorInt::FailedPrecondition(format!(
                "{} CSeq {} is still awaiting its response",
                p.req.method_str(),
                p.cseq
            )));
        }
        let cseq = self.fill_req(&mut req)?;
        self.queue(&req);
        self.pending = Some(Pending { req, cseq, mode });
        Ok(())
    }

    /// Returns the bytes to write to the connection, in order.
    ///
    /// The first slice is empty iff there's nothing to write.
    pub(crate) fn transmit_buf(&self) -> (&[u8], &[u8]) {
        self.transmit.slices()
    }

    /// Notes that the first `n` bytes of [`ConnCore::transmit_buf`] have been
    /// written.
    pub(crate) fn advance_transmit(&mut self, n: usize) {
        self.transmit.advance(n);
    }

    /// Forgets the pending request, if any, so that another can be sent.
    ///
    /// A late response to it would be unexpected, so this is only suitable
    /// before a `TEARDOWN`, which ignores unrelated responses.
    pub(crate) fn abandon_pending(&mut self) {
        self.pending = None;
    }

    /// Returns the response to the pending request, once it's been received.
    ///
    /// Returns `None` if more data is needed, or if no request is pending; in
    /// the latter case, data is left buffered for later. On error, the
    /// request is no longer pending.
    pub(crate) fn poll_response(&mut self, now: Instant) -> Option<Result<Response, Error>> {
        let r = self.poll_response_inner(now)?;
        if r.is_err() {
            self.pending = None;
        }
        Some(r)
    }

    fn poll_response_inner(&mut self, now: Instant) -> Option<Result<Response, Error>> {
        loop {
            let pending = self.pending.as_ref()?;
            let (cseq, mode) = (pending.cseq, pending.mode);
            let msg = match self.reader.decode(&self.ctx, self.eof, now) {
                Err(e) => return Some(Err(e)),
                Ok(Some(msg)) => msg,
                Ok(None) if !self.eof => return None,
                Ok(None) => {
                    return Some(Err(wrap!(ErrorInt::RtspReadError {
                        conn_ctx: self.ctx,
                        msg_ctx: self.reader.eof_ctx(now),
                        source: std::io::Error::new(
                            std::io::ErrorKind::UnexpectedEof,
                            format!(
                                "EOF while expecting response to {} CSeq {cseq}",
                                pending.req.method_str()
                            ),
                        ),
                    })));
                }
            };
            let msg_ctx = msg.ctx;
            let description = match msg.msg {
                msg::Message::Response(r) => {
                    if let Some(response_cseq) = parse::get_cseq(&r) {
                        if response_cseq == cseq {
                            let body = self.reader.body_bytes(msg.body_pos, msg.body_len);
                            match self.handle_response(msg_ctx, r, body) {
                                Ok(None) => continue, // retrying with authentication.
                                Ok(Some(r)) => return Some(Ok(r)),
                                Err(e) => return Some(Err(e)),
                            }
                        }
                        if matches!(mode, ResponseMode::Teardown) {
                            debug!("ignoring unrelated response during TEARDOWN");
                            continue;
                        }
                        format!("{} response with CSeq {}", r.reason_phrase, response_cseq)
                    } else {
                        format!("{} response with no/unparseable cseq", r.reason_phrase)
                    }
                }
                msg::Message::Data(d) => {
                    if matches!(mode, ResponseMode::Teardown) {
                        debug!("ignoring RTSP interleaved data during TEARDOWN");
                        continue;
                    } else if let (ResponseMode::Play, Some(m)) =
                        (mode, self.channels.lookup(d.channel_id))
                    {
                        debug!(
                            "ignoring interleaved data message on {:?} channel {} while \
                             waiting for response to PLAY CSeq {}",
                            m.channel_type, d.channel_id, cseq
                        );
                        continue;
                    }
                    let body = self.reader.body_bytes(msg.body_pos, msg.body_len);
                    if let Err(e) =
                        super::handle_unassigned_data(self, msg_ctx, d.channel_id, body, now)
                    {
                        return Some(Err(e));
                    }
                    continue;
                }
                msg::Message::Request(r) => format!("{:?} request", r.method),
            };
            let method = pending.req.method_str();
            return Some(Err(wrap!(ErrorInt::RtspFramingError {
                conn_ctx: self.ctx,
                msg_ctx,
                description: format!(
                    "Expected response to {method} CSeq {cseq}, got {description}"
                ),
            })));
        }
    }

    /// Handles the response to the pending request.
    ///
    /// Returns `Ok(None)` if the request has been resent with authentication.
    fn handle_response(
        &mut self,
        msg_ctx: RtspMessageContext,
        head: msg::Response,
        body: Bytes,
    ) -> Result<Option<Response>, Error> {
        let Pending {
            mut req,
            cseq,
            mode,
        } = self.pending.take().expect("pending");
        let response = Response {
            msg_ctx,
            cseq,
            method: req.method().clone(),
            head,
            body,
        };
        if response.head.status_code == StatusCode::UNAUTHORIZED {
            if self.requested_auth.is_some() {
                // TODO: the WWW-Authenticate might indicate a new domain or nonce.
                // In that case, we should retry rather than returning error.
                return Err(response.error(
                    &self.ctx,
                    "Received Unauthorized after trying digest auth".into(),
                ));
            }
            let Some(www_authenticate) = response.head.headers.get("WWW-Authenticate") else {
                return Err(response.error(
                    &self.ctx,
                    "Unauthorized without WWW-Authenticate header".into(),
                ));
            };
            if self.options.creds.is_none() {
                return Err(response.error(
                    &self.ctx,
                    "Authentication requested and no credentials supplied".into(),
                ));
            }
            let www_authenticate: &str = www_authenticate;
            self.requested_auth = match http_auth::PasswordClient::try_from(www_authenticate) {
                Ok(c) => Some(c),
                Err(e) => {
                    return Err(response.error(
                        &self.ctx,
                        format!("Can't understand WWW-Authenticate header: {e}"),
                    ));
                }
            };
            let cseq = self.fill_req(&mut req)?;
            self.queue(&req);
            self.pending = Some(Pending { req, cseq, mode });
            return Ok(None);
        }
        if !response.head.status_code.is_success() {
            return Err(response.error(&self.ctx, "Unexpected RTSP response status".into()));
        }
        Ok(Some(response))
    }
}
