// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The sans-I/O core of a playing session; see [`PlayingCore`].

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use bytes::Bytes;
use log::{trace, warn};
use url::Url;

use super::channel_mapping::{ChannelMappings, ChannelType};
use super::parse::{self, SessionHeader};
use super::receiver_report::{ReceptionStats, ReportSchedule, ReportWriter};
use super::{PlayingItem, RtpPacket, SessionOptions, Stream, Timeline, Tool, rtp::InorderParser};
use crate::buf::MarkBuf;
use crate::rtsp::msg::{self, OwnedMessage};
use crate::rtsp::reader::Reader;
use crate::{
    ConnectionContext, Error, ErrorInt, PacketContext, PacketContextInner, RtspMessageContext,
    StreamContext, WallTime,
};

/// The sans-I/O core of a [`super::Session<super::Playing>`].
///
/// This holds all the state of a playing session except for sockets and
/// timers: the RTSP parser and the buffers received data is read into, each
/// stream's RTP validation state, and keepalive and RTCP receiver report
/// state. Time is supplied by the caller. The session is a thin driver around
/// it:
///
/// *   It reads from the RTSP connection into [`PlayingCore::tcp_buf`] and
///     from each UDP stream's sockets into [`PlayingCore::udp_buf`] (followed
///     by [`PlayingCore::udp_received`]).
/// *   It gets packets out via [`PlayingCore::poll_validated`] and
///     [`PlayingCore::item`].
/// *   It writes keepalive requests and interleaved receiver reports from
///     [`PlayingCore::poll_transmit`], reporting when they've been flushed via
///     [`PlayingCore::handle_flushed`].
/// *   It sends UDP streams' receiver reports from
///     [`PlayingCore::poll_transmit_udp`].
/// *   It calls [`PlayingCore::handle_timeout`] at
///     [`PlayingCore::poll_timeout`].
pub(crate) struct PlayingCore {
    conn_ctx: ConnectionContext,
    reader: Reader,

    /// True if the peer has closed the RTSP connection.
    tcp_eof: bool,

    channels: ChannelMappings,

    /// True if data has been received on an unassigned interleaved channel.
    seen_unassigned: bool,

    /// State for each stream in the presentation which has been set up.
    streams: Box<[Option<PlayingStream>]>,

    /// UDP datagrams which have been received but not yet parsed, in order.
    udp_pending: VecDeque<StreamItem>,

    options: SessionOptions,
    requested_auth: Option<http_auth::PasswordClient>,
    tool: Option<Tool>,
    next_cseq: u32,
    keepalive: Keepalive,

    /// The state of RTCP receiver reports, iff they're enabled via
    /// [`SessionOptions::receiver_reports`].
    reports: Option<Reports>,

    /// Keepalive requests and interleaved receiver reports for the RTSP
    /// connection.
    transmit: Transmit,

    /// Receiver reports for UDP streams, as `(stream_i, packet)`, which have
    /// yet to be returned from `poll_transmit_udp`.
    transmit_udp: VecDeque<(usize, Vec<u8>)>,
}

/// Bytes for [`PlayingCore::poll_transmit`].
#[derive(Default)]
struct Transmit {
    buf: Vec<u8>,

    /// True if `buf` has yet to be returned from `poll_transmit`.
    ready: bool,
}

impl Transmit {
    /// Appends `msg` to any bytes not yet returned.
    fn queue(&mut self, msg: OwnedMessage) {
        if !self.ready {
            self.buf.clear();
        }
        msg.write(&mut self.buf).expect("Vec Writer is infallible");
        self.ready = true;
    }
}

/// The state of RTCP receiver reports.
pub(crate) struct Reports {
    pub(crate) writer: ReportWriter,
    schedule: ReportSchedule,

    /// When the next reports are due: normally `schedule.next_due()`, but
    /// tests may move it.
    pub(crate) due: Instant,
}

/// The state of a stream which has been set up.
pub(crate) struct PlayingStream {
    pub(crate) timeline: Timeline,
    pub(crate) rtp_handler: InorderParser,
    pub(crate) ctx: StreamContext,

    /// For a UDP stream, the buffer which datagrams are received into.
    pub(crate) udp_buf: Option<MarkBuf>,

    /// Reception statistics for RTCP receiver reports, iff they're enabled.
    pub(crate) reception: Option<ReceptionStats>,
}

/// Session state moved into [`PlayingCore::new`], to be returned by
/// [`PlayingCore::into_parts`] when the session is dropped.
pub(crate) struct Parts {
    pub(crate) reader: Reader,
    pub(crate) options: SessionOptions,
    pub(crate) requested_auth: Option<http_auth::PasswordClient>,
    pub(crate) next_cseq: u32,
}

/// Everything else [`PlayingCore::new`] needs.
pub(crate) struct Init<'a> {
    pub(crate) conn_ctx: ConnectionContext,
    pub(crate) channels: ChannelMappings,
    pub(crate) seen_unassigned: bool,
    pub(crate) streams: Box<[Option<PlayingStream>]>,
    pub(crate) tool: Option<Tool>,
    pub(crate) session: &'a SessionHeader,

    /// The URL keepalive requests are sent to.
    pub(crate) keepalive_url: Url,
}

struct Keepalive {
    state: KeepaliveState,
    deadline: Instant,
    interval: Duration,
    url: Url,
    session_id: msg::HeaderValue,

    /// Set if an `OPTIONS` response has advertised support for `SET_PARAMETER`.
    set_parameter_supported: bool,

    /// Set if an `OPTIONS` response has advertised support for `GET_PARAMETER`.
    get_parameter_supported: bool,
}

#[derive(Copy, Clone, Debug)]
enum KeepaliveState {
    Idle,
    Flushing { cseq: u32, method: KeepaliveMethod },
    Waiting { cseq: u32, method: KeepaliveMethod },
}

#[derive(Copy, Clone, Debug)]
enum KeepaliveMethod {
    Options,
    SetParameter,
    GetParameter,
}

impl From<KeepaliveMethod> for msg::Method {
    fn from(method: KeepaliveMethod) -> Self {
        match method {
            KeepaliveMethod::Options => msg::Method::OPTIONS,
            KeepaliveMethod::SetParameter => msg::Method::SET_PARAMETER,
            KeepaliveMethod::GetParameter => msg::Method::GET_PARAMETER,
        }
    }
}

/// Returns an appropriate keepalive interval for `session`.
///
/// This generally uses half the session timeout. However, it's capped in case
/// the server offers a generous timeout, messages are rare (e.g. ONVIF metadata
/// streams), and there's a NAT box between with a shorter timeout.
fn keepalive_interval(session: &SessionHeader) -> Duration {
    Duration::from_secs(std::cmp::min(u64::from(session.timeout_sec), 60)) / 2
}

/// Raw received packet before validation.
struct StreamItem {
    pkt_ctx: PacketContext,
    stream_i: usize,
    channel_type: ChannelType,
    body_pos: u64,
    body_len: u16,
}

/// A validated RTP or RTCP packet; [`PlayingCore::item`] turns this into a
/// [`PlayingItem`].
///
/// This is separate from [`PlayingItem`] because returning a borrow from the
/// driver's polling loop would be rejected by the borrow checker.
pub(crate) enum ValidatedItem {
    Rtcp(crate::rtcp::ReceivedCompoundPacket),
    Rtp(ValidatedRtp),
}

/// Metadata for a validated RTP packet whose body is in a ring buffer.
pub(crate) struct ValidatedRtp {
    stream_id: usize,
    meta: crate::rtp::PacketMeta<PacketContext>,
    body_pos: u64,
    body_len: u16,
    payload_range: std::ops::Range<u16>,
}

impl PlayingCore {
    pub(crate) fn new(parts: Parts, init: Init<'_>, now: Instant) -> Self {
        let interval = keepalive_interval(init.session);
        let reports = parts.options.receiver_reports.enabled().then(|| {
            let mut rng = rand::thread_rng();
            let schedule = ReportSchedule::new(now, &mut rng);
            Reports {
                writer: ReportWriter::random(&mut rng),
                due: schedule.next_due(),
                schedule,
            }
        });
        Self {
            conn_ctx: init.conn_ctx,
            reader: parts.reader,
            tcp_eof: false,
            channels: init.channels,
            seen_unassigned: init.seen_unassigned,
            streams: init.streams,
            udp_pending: VecDeque::new(),
            options: parts.options,
            requested_auth: parts.requested_auth,
            tool: init.tool,
            next_cseq: parts.next_cseq,
            keepalive: Keepalive {
                state: KeepaliveState::Idle,
                deadline: now + interval,
                interval,
                url: init.keepalive_url,
                session_id: init.session.id.clone(),
                set_parameter_supported: false,
                get_parameter_supported: false,
            },
            reports,
            transmit: Transmit::default(),
            transmit_udp: VecDeque::new(),
        }
    }

    /// Returns the state moved in by [`PlayingCore::new`].
    pub(crate) fn into_parts(self) -> Parts {
        Parts {
            reader: self.reader,
            options: self.options,
            requested_auth: self.requested_auth,
            next_cseq: self.next_cseq,
        }
    }

    /// Returns the buffer the caller should fill with bytes received on the
    /// RTSP connection, via `spare_capacity` and `advance_end`.
    #[inline]
    pub(crate) fn tcp_buf(&mut self) -> &mut MarkBuf {
        self.reader.buf_mut()
    }

    /// Notes that the peer has closed the RTSP connection.
    ///
    /// Once [`PlayingCore::poll_validated`] has returned the remaining items,
    /// [`PlayingCore::is_closed`] is true.
    pub(crate) fn handle_tcp_eof(&mut self) {
        self.tcp_eof = true;
    }

    /// Returns true if no more items will be returned, because the peer has
    /// closed the RTSP connection.
    pub(crate) fn is_closed(&self) -> bool {
        self.tcp_eof
    }

    /// Returns the buffer the caller should read a datagram for UDP stream
    /// `stream_i` into, via `spare_capacity`. Follow with
    /// [`PlayingCore::udp_received`].
    ///
    /// Panics if the stream isn't a set-up UDP stream.
    pub(crate) fn udp_buf(&mut self, stream_i: usize) -> &mut MarkBuf {
        self.streams[stream_i]
            .as_mut()
            .and_then(|s| s.udp_buf.as_mut())
            .expect("udp_buf requires a UDP stream")
    }

    /// Notes that a `len`-byte datagram was written to the start of
    /// [`PlayingCore::udp_buf`]'s spare capacity.
    ///
    /// The caller may receive several datagrams before calling
    /// [`PlayingCore::poll_validated`]; they stay in the buffer until parsed.
    pub(crate) fn udp_received(
        &mut self,
        stream_i: usize,
        channel_type: ChannelType,
        len: u16,
        now: Instant,
    ) {
        let buf = self.udp_buf(stream_i);
        let body_pos = buf.end();
        buf.advance_end(usize::from(len));
        self.udp_pending.push_back(StreamItem {
            pkt_ctx: PacketContext(PacketContextInner::Udp {
                received: now,
                received_wall: WallTime::now(),
            }),
            stream_i,
            channel_type,
            body_pos,
            body_len: len,
        });
    }

    /// Returns a context for the RTSP connection.
    #[inline]
    pub(crate) fn conn_ctx(&self) -> &ConnectionContext {
        &self.conn_ctx
    }

    /// Returns an error for a failed read from the RTSP connection.
    pub(crate) fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.reader.read_error(&self.conn_ctx, source, now)
    }

    /// Parses and validates the next packet from buffered data, if any.
    ///
    /// Returns `None` when more data is needed (or, if
    /// [`PlayingCore::is_closed`], never will be). Handles keepalive
    /// responses internally.
    pub(crate) fn poll_validated(&mut self, now: Instant) -> Option<Result<ValidatedItem, Error>> {
        loop {
            let item = match self.reader.decode(&self.conn_ctx, self.tcp_eof, now) {
                Err(e) => return Some(Err(e)),
                Ok(Some(msg)) => match msg.msg {
                    msg::Message::Data(d) => {
                        match self.handle_data(&msg.ctx, d.channel_id, msg.body_pos, d.body_len) {
                            Err(e) => return Some(Err(e)),
                            Ok(None) => continue,
                            Ok(Some(item)) => item,
                        }
                    }
                    msg::Message::Response(response) => {
                        if let Err(e) = self.handle_response(&msg.ctx, response) {
                            return Some(Err(e));
                        }
                        continue;
                    }
                    msg::Message::Request(request) => {
                        warn!(
                            "Received RTSP request in Playing state. Responding unimplemented.\n{:#?}",
                            request
                        );
                        continue;
                    }
                },
                Ok(None) => {
                    let item = self.udp_pending.pop_front()?;
                    self.udp_buf(item.stream_i)
                        .advance_unparsed(item.body_pos + u64::from(item.body_len));
                    item
                }
            };
            match self.validate(item, now) {
                Err(e) => return Some(Err(e)),
                Ok(None) => {}
                Ok(Some(v)) => return Some(Ok(v)),
            }
        }
    }

    /// Builds a [`PlayingItem`] which borrows the core's buffers and `streams`.
    pub(crate) fn item<'a>(&'a self, streams: &'a [Stream], v: ValidatedItem) -> PlayingItem<'a> {
        let rtp = match v {
            ValidatedItem::Rtcp(pkt) => return PlayingItem::Rtcp(pkt),
            ValidatedItem::Rtp(rtp) => rtp,
        };
        let buf = self.streams[rtp.stream_id]
            .as_ref()
            .and_then(|s| s.udp_buf.as_ref())
            .unwrap_or(self.reader.buf());
        PlayingItem::Rtp(RtpPacket {
            stream_id: rtp.stream_id,
            stream: &streams[rtp.stream_id],
            pkt: crate::buf::PacketRef::new(
                rtp.meta,
                buf,
                rtp.body_pos + u64::from(rtp.payload_range.start),
                rtp.payload_range.end - rtp.payload_range.start,
            ),
            raw_pos: rtp.body_pos,
            raw_len: rtp.body_len,
        })
    }

    /// Combines [`PlayingCore::poll_validated`] and [`PlayingCore::item`].
    #[cfg(test)]
    pub(crate) fn poll_item<'a>(
        &'a mut self,
        streams: &'a [Stream],
        now: Instant,
    ) -> Option<Result<PlayingItem<'a>, Error>> {
        match self.poll_validated(now)? {
            Ok(v) => Some(Ok(self.item(streams, v))),
            Err(e) => Some(Err(e)),
        }
    }

    /// Returns the next time [`PlayingCore::handle_timeout`] should be called.
    #[inline]
    pub(crate) fn poll_timeout(&self) -> Instant {
        match &self.reports {
            Some(r) => self.keepalive.deadline.min(r.due),
            None => self.keepalive.deadline,
        }
    }

    /// Handles the passage of time, starting a keepalive request and/or
    /// writing receiver reports if due.
    ///
    /// Returns an error if the previous keepalive hasn't been flushed or
    /// answered in time.
    pub(crate) fn handle_timeout(&mut self, now: Instant) -> Result<(), Error> {
        if now >= self.keepalive.deadline {
            self.send_keepalive(now)?;
        }
        if self.reports.as_ref().is_some_and(|r| now >= r.due) {
            self.send_reports(now);
        }
        Ok(())
    }

    /// Starts a keepalive request, which is due.
    fn send_keepalive(&mut self, now: Instant) -> Result<(), Error> {
        let keepalive = &mut self.keepalive;
        let interval = keepalive.interval;

        // Expect the previous keepalive request to have finished.
        match keepalive.state {
            KeepaliveState::Flushing { cseq, .. } => bail!(ErrorInt::WriteError {
                conn_ctx: self.conn_ctx,
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!("Unable to write keepalive {cseq} within {interval:?}",),
                ),
            }),
            KeepaliveState::Waiting { cseq, .. } => bail!(ErrorInt::RtspReadError {
                conn_ctx: self.conn_ctx,
                msg_ctx: self.reader.eof_ctx(now),
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!("Server failed to respond to keepalive {cseq} within {interval:?}",),
                ),
            }),
            KeepaliveState::Idle => {}
        }

        // Send a new keepalive.
        //
        // RTSP/1.0 (the version Retina implements) doesn't describe how to send
        // a keepalive. The ONVIF Streaming Specification (in version 21.06 section
        // 5.2.2.2
        // <https://www.onvif.org/specs/stream/ONVIF-Streaming-Spec.pdf>) and
        // RTSP/2.0 recommend using `SET_PARAMETER`. However, this method is optional,
        // and some servers (e.g. rtsp-simple-server as of 2021-08-07) behave badly
        // on receiving unsupported methods. See discussion at
        // <https://github.com/aler9/rtsp-simple-server/issues/1066>. Initially
        // send `OPTIONS`, then use (bodyless) `GET_PARAMETER` or `SET_PARAMETER`
        // if available.
        //
        // Prefer `GET_PARAMETER` over `SET_PARAMETER`, contrary to the ONVIF
        // recommendation. Tapo cameras advertise `SET_PARAMETER` but reply to it
        // with `400 Bad Request` with the previous request's `CSeq`, while handling
        // `GET_PARAMETER` correctly. ffmpeg also prefers `GET_PARAMETER` (and never
        // uses `SET_PARAMETER` for keepalives), so this is likely the more
        // well-tested choice in general.
        let method = if keepalive.get_parameter_supported {
            KeepaliveMethod::GetParameter
        } else if keepalive.set_parameter_supported {
            KeepaliveMethod::SetParameter
        } else {
            KeepaliveMethod::Options
        };
        let mut req = OwnedMessage::Request {
            head: msg::Request {
                method: method.into(),
                request_uri: Some(keepalive.url.clone()),
                headers: [(msg::HeaderName::SESSION, keepalive.session_id.clone())].into(),
            },
            body: Bytes::new(),
        };
        let cseq = super::fill_req(
            &mut self.next_cseq,
            &self.options,
            &mut self.requested_auth,
            &mut req,
        )?;
        trace!("sending {:?} keepalive", method);
        self.transmit.queue(req);
        let keepalive = &mut self.keepalive;
        keepalive.state = KeepaliveState::Flushing { cseq, method };
        keepalive.deadline = now + interval;
        Ok(())
    }

    /// Writes a receiver report for each stream, which are due, and schedules
    /// the next.
    ///
    /// Each stream is its own RTP session, so each gets its own report on its
    /// own RTCP channel or socket. Over TCP, the report is queued for
    /// [`PlayingCore::poll_transmit`] (after any keepalive). Over UDP, it's
    /// queued for [`PlayingCore::poll_transmit_udp`].
    fn send_reports(&mut self, now: Instant) {
        let reports = self.reports.as_mut().expect("reports are enabled");
        for (i, s) in self.streams.iter_mut().enumerate() {
            let Some(PlayingStream {
                ctx,
                udp_buf,
                reception: Some(reception),
                ..
            }) = s
            else {
                continue;
            };
            let block = reception.report_block(now);
            trace!("sending RTCP receiver report for stream {i}: {block:?}");
            let pkt = reports.writer.write(block.as_ref());
            match (udp_buf, &ctx.0) {
                (Some(_), _) => self.transmit_udp.push_back((i, pkt)),
                (None, crate::StreamContextInner::Tcp(tcp)) => {
                    self.transmit.queue(OwnedMessage::Data {
                        channel_id: tcp.rtp_channel_id + 1,
                        body: Bytes::from(pkt),
                    })
                }
                (None, _) => unreachable!("stream {i} has neither TCP nor UDP context"),
            }
        }
        reports.schedule.sent(now, &mut rand::thread_rng());
        reports.due = reports.schedule.next_due();
    }

    /// Returns bytes to write to the RTSP connection, if any.
    ///
    /// Each call returns new bytes; the caller should buffer them and call
    /// [`PlayingCore::handle_flushed`] once they've all been written.
    pub(crate) fn poll_transmit(&mut self) -> Option<&[u8]> {
        if !self.transmit.ready {
            return None;
        }
        self.transmit.ready = false;
        Some(&self.transmit.buf)
    }

    /// Returns a receiver report to send on UDP stream `stream_i`'s RTCP
    /// socket, as `(stream_i, packet)`, if any.
    ///
    /// The caller should send it right away if the socket has room and
    /// otherwise drop it, as later reports carry cumulative statistics anyway.
    pub(crate) fn poll_transmit_udp(&mut self) -> Option<(usize, Vec<u8>)> {
        self.transmit_udp.pop_front()
    }

    /// Moves the keepalive deadline; follow by resetting the driver's timer.
    #[cfg(test)]
    pub(crate) fn set_keepalive_deadline(&mut self, deadline: Instant) {
        self.keepalive.deadline = deadline;
    }

    /// Pretends an `OPTIONS` response advertised `GET_PARAMETER` and
    /// `SET_PARAMETER`.
    #[cfg(test)]
    pub(crate) fn set_parameter_methods_supported(&mut self) {
        self.keepalive.get_parameter_supported = true;
        self.keepalive.set_parameter_supported = true;
    }

    /// Returns the receiver report state, iff reports are enabled. Follow a
    /// change to `due` by resetting the driver's timer.
    #[cfg(test)]
    pub(crate) fn reports_mut(&mut self) -> Option<&mut Reports> {
        self.reports.as_mut()
    }

    /// Returns true if any stream keeps reception statistics.
    #[cfg(test)]
    pub(crate) fn has_reception_stats(&self) -> bool {
        self.streams
            .iter()
            .any(|s| s.as_ref().is_some_and(|s| s.reception.is_some()))
    }

    /// Notes that all bytes returned by [`PlayingCore::poll_transmit`] have
    /// been written.
    pub(crate) fn handle_flushed(&mut self) {
        if let KeepaliveState::Flushing { cseq, method } = self.keepalive.state {
            self.keepalive.state = KeepaliveState::Waiting { cseq, method };
        }
    }

    fn handle_response(
        &mut self,
        msg_ctx: &RtspMessageContext,
        response: msg::Response,
    ) -> Result<(), Error> {
        let keepalive = &mut self.keepalive;
        if let KeepaliveState::Waiting { cseq, method } = keepalive.state
            && parse::get_cseq(&response) == Some(cseq)
        {
            // We don't care if the keepalive response succeeds or fails, but we should
            // log it, to help debugging if on failure the server doesn't extend the
            // timeout or gets angry and closes the connection. (rtsp-simple-server
            // does the latter as of 2022-08-07, though I'm told this will be fixed.)
            if !response.status_code.is_success() {
                warn!("keepalive failed with {:?}", response.status_code);
            } else {
                trace!("keepalive succeeded with {:?}", response.status_code);
                if matches!(method, KeepaliveMethod::Options) {
                    match parse::parse_options(&response) {
                        Ok(r) => {
                            keepalive.set_parameter_supported |= r.set_parameter_supported;
                            keepalive.get_parameter_supported |= r.get_parameter_supported;
                        }
                        Err(e) => {
                            warn!("Unable to parse OPTIONS response: {}", e);
                        }
                    }
                }
            }
            keepalive.state = KeepaliveState::Idle;
            return Ok(());
        }

        // The only response we expect in this state is to our keepalive request.
        bail!(ErrorInt::RtspFramingError {
            conn_ctx: self.conn_ctx,
            msg_ctx: *msg_ctx,
            description: format!("Unexpected RTSP response {response:#?}"),
        })
    }

    /// Maps an interleaved TCP data message to a [`StreamItem`].
    ///
    /// Handles unassigned channels (returning `Ok(None)`); validation is
    /// deferred to [`PlayingCore::validate`].
    fn handle_data(
        &mut self,
        msg_ctx: &RtspMessageContext,
        channel_id: u8,
        body_pos: u64,
        body_len: u16,
    ) -> Result<Option<StreamItem>, Error> {
        let Some(m) = self.channels.lookup(channel_id) else {
            let body = self.reader.body_bytes(body_pos, u32::from(body_len));
            super::handle_unassigned_data(
                &self.conn_ctx,
                &mut self.seen_unassigned,
                *msg_ctx,
                &self.options,
                self.tool.as_ref(),
                channel_id,
                body,
            )?;
            return Ok(None);
        };
        Ok(Some(StreamItem {
            pkt_ctx: PacketContext(PacketContextInner::Tcp { msg_ctx: *msg_ctx }),
            stream_i: m.stream_i,
            channel_type: m.channel_type,
            body_pos,
            body_len,
        }))
    }

    /// Validates a raw [`StreamItem`], returning a [`ValidatedItem`] or `None`
    /// if the packet should be skipped.
    ///
    /// This is the single processing point for both TCP and UDP paths:
    /// RTP header validation, `rtp_handler.rtp()`, and `rtp_handler.rtcp()`
    /// all happen here.
    fn validate(&mut self, item: StreamItem, now: Instant) -> Result<Option<ValidatedItem>, Error> {
        let stream = self.streams[item.stream_i]
            .as_mut()
            .expect("only set-up streams have packets");
        let buf = stream.udp_buf.as_ref().unwrap_or(self.reader.buf());
        match item.channel_type {
            ChannelType::Rtp => {
                let split = buf.split(item.body_pos, usize::from(item.body_len));
                let (header, payload_range) =
                    crate::rtp::PacketHeader::validate(split).map_err(|reason| {
                        wrap!(ErrorInt::PacketError {
                            conn_ctx: self.conn_ctx,
                            stream_ctx: stream.ctx,
                            pkt_ctx: item.pkt_ctx,
                            stream_id: item.stream_i,
                            description: stream.rtp_handler.validate_error(reason, split),
                        })
                    })?;

                // Count the packet for receiver reports as it arrives, before
                // `rtp_handler` skips or rejects it for being out of order: RFC
                // 3550 appendix A.1 counts reordered and duplicate packets as
                // received. Like `rtp_handler`, ignore pt=50 packets.
                if let Some(reception) = &mut stream.reception
                    && header.payload_type() != 50
                {
                    reception.rtp(
                        header.ssrc(),
                        header.sequence_number(),
                        header.timestamp(),
                        now,
                    );
                }
                let Some(meta) = stream.rtp_handler.rtp(
                    &self.options,
                    &stream.ctx,
                    self.tool.as_ref(),
                    &self.conn_ctx,
                    &item.pkt_ctx,
                    &mut stream.timeline,
                    item.stream_i,
                    &header,
                )?
                else {
                    return Ok(None);
                };
                Ok(Some(ValidatedItem::Rtp(ValidatedRtp {
                    stream_id: item.stream_i,
                    meta,
                    body_pos: item.body_pos,
                    body_len: item.body_len,
                    payload_range,
                })))
            }
            ChannelType::Rtcp => {
                let body = Bytes::from(
                    buf.split(item.body_pos, usize::from(item.body_len))
                        .to_vec(),
                );
                match stream.rtp_handler.rtcp(
                    &self.options,
                    &stream.ctx,
                    self.tool.as_ref(),
                    &self.conn_ctx,
                    &item.pkt_ctx,
                    &mut stream.timeline,
                    item.stream_i,
                    body,
                ) {
                    Ok(p) => {
                        // Note sender reports for the LSR and DLSR fields of
                        // receiver reports. `rtp_handler` has already checked
                        // the SSRC (per `UnknownRtcpSsrcPolicy`) and set
                        // `rtp_timestamp` iff the packet begins with a valid
                        // sender report.
                        if let (Some(reception), Some(pkt)) = (&mut stream.reception, &p)
                            && pkt.rtp_timestamp().is_some()
                            && let Some(Ok(Some(sr))) =
                                pkt.pkts().next().map(|p| p.as_sender_report())
                        {
                            reception.sender_report(sr.ssrc(), sr.ntp_timestamp(), now);
                        }
                        Ok(p.map(ValidatedItem::Rtcp))
                    }
                    Err(description) => Err(wrap!(ErrorInt::PacketError {
                        conn_ctx: self.conn_ctx,
                        stream_ctx: stream.ctx,
                        pkt_ctx: item.pkt_ctx,
                        stream_id: item.stream_i,
                        description,
                    })),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::UnknownRtcpSsrcPolicy;

    const INTERVAL: Duration = Duration::from_secs(30);

    /// A core for the Reolink presentation, with its video stream (0) set up
    /// via TCP on channels 0–1 and its audio stream (1) via UDP.
    struct Fixture {
        core: PlayingCore,
        streams: Box<[Stream]>,
        t0: Instant,
    }

    fn fixture() -> Fixture {
        crate::testutil::init_logging();
        let (resp, body) =
            crate::testutil::response(include_bytes!("testdata/reolink_describe.txt"));
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let presentation = parse::parse_describe(url, &resp, &body).unwrap();
        let mut channels = ChannelMappings::default();
        channels.assign(0, 0).unwrap();
        let new_stream = |s: &Stream, udp: bool| {
            Some(PlayingStream {
                timeline: Timeline::new(None, s.clock_rate_hz(), None).unwrap(),
                rtp_handler: InorderParser::new(None, None, UnknownRtcpSsrcPolicy::Default),
                ctx: StreamContext::dummy(),
                udp_buf: udp.then(|| MarkBuf::new(65536)),
                reception: None,
            })
        };
        let streams = [
            new_stream(&presentation.streams[0], false),
            new_stream(&presentation.streams[1], true),
        ];
        let t0 = Instant::now();
        let core = PlayingCore::new(
            Parts {
                reader: Reader::default(),
                options: SessionOptions::default(),
                requested_auth: None,
                next_cseq: 5,
            },
            Init {
                conn_ctx: ConnectionContext::dummy(),
                channels,
                seen_unassigned: false,
                streams: streams.into(),
                tool: None,
                session: &SessionHeader {
                    id: msg::HeaderValue::try_from("F8F8E425").unwrap(),
                    timeout_sec: 60,
                },
                keepalive_url: presentation.base_url.clone(),
            },
            t0,
        );
        Fixture {
            core,
            streams: presentation.streams,
            t0,
        }
    }

    /// Returns the request passed to `poll_transmit`, which must be exactly one.
    fn transmitted(core: &mut PlayingCore) -> String {
        let req = String::from_utf8(core.poll_transmit().expect("should transmit").to_vec());
        assert!(core.poll_transmit().is_none());
        req.unwrap()
    }

    /// Returns an interleaved data message holding an RTP packet.
    fn interleaved(channel_id: u8, sequence_number: u16, payload: &[u8]) -> Vec<u8> {
        let pkt = crate::rtp::build_raw_rtp(
            sequence_number,
            0,
            96,
            0xdcc4a0d8,
            true,
            payload.iter().copied(),
        )
        .unwrap();
        let mut msg = vec![b'$', channel_id];
        msg.extend_from_slice(&u16::try_from(pkt.len()).unwrap().to_be_bytes());
        msg.extend_from_slice(&pkt);
        msg
    }

    #[test]
    fn keepalive_timing() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        assert_eq!(core.poll_timeout(), t0 + INTERVAL);

        // Nothing is sent before the deadline.
        core.handle_timeout(t0 + INTERVAL - Duration::from_millis(1))
            .unwrap();
        assert!(core.poll_transmit().is_none());

        // At the deadline, an `OPTIONS` goes out, and the next deadline is set.
        let t1 = t0 + INTERVAL;
        core.handle_timeout(t1).unwrap();
        let req = transmitted(&mut core);
        assert!(
            req.starts_with("OPTIONS rtsp://192.168.5.206/h264Preview_01_main/ RTSP/1.0\r\n"),
            "{req}"
        );
        assert!(req.contains("\r\nCSeq: 5\r\n"), "{req}");
        assert!(req.contains("\r\nSession: F8F8E425\r\n"), "{req}");
        assert_eq!(core.poll_timeout(), t1 + INTERVAL);
        core.handle_flushed();

        // The response advertises `SET_PARAMETER`; it's used from then on.
        core.tcp_buf().extend(
            b"RTSP/1.0 200 OK\r\nCSeq: 5\r\n\
              Public: OPTIONS, DESCRIBE, SETUP, PLAY, TEARDOWN, SET_PARAMETER\r\n\r\n",
        );
        assert!(core.poll_item(&streams, t1).is_none());
        let t2 = t1 + INTERVAL;
        core.handle_timeout(t2).unwrap();
        let req = transmitted(&mut core);
        assert!(req.starts_with("SET_PARAMETER "), "{req}");
        assert!(req.contains("\r\nCSeq: 6\r\n"), "{req}");
    }

    /// A failed keepalive is only logged, and doesn't change the method.
    #[test]
    fn keepalive_error_response() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        let t1 = t0 + INTERVAL;
        core.handle_timeout(t1).unwrap();
        assert!(transmitted(&mut core).starts_with("OPTIONS "));
        core.handle_flushed();
        core.tcp_buf()
            .extend(b"RTSP/1.0 454 Session Not Found\r\nCSeq: 5\r\n\r\n");
        assert!(core.poll_item(&streams, t1).is_none());
        core.handle_timeout(t1 + INTERVAL).unwrap();
        assert!(transmitted(&mut core).starts_with("OPTIONS "));
    }

    #[test]
    fn keepalive_unanswered() {
        let Fixture { mut core, t0, .. } = fixture();
        core.handle_timeout(t0 + INTERVAL).unwrap();
        transmitted(&mut core);
        core.handle_flushed();
        let e = core.handle_timeout(t0 + 2 * INTERVAL).unwrap_err();
        assert!(
            e.to_string()
                .contains("Server failed to respond to keepalive 5 within 30s"),
            "{e}"
        );
    }

    #[test]
    fn keepalive_unflushed() {
        let Fixture { mut core, t0, .. } = fixture();
        core.handle_timeout(t0 + INTERVAL).unwrap();
        transmitted(&mut core);
        let e = core.handle_timeout(t0 + 2 * INTERVAL).unwrap_err();
        assert!(
            e.to_string()
                .contains("Unable to write keepalive 5 within 30s"),
            "{e}"
        );
    }

    #[test]
    fn unexpected_response() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        core.tcp_buf()
            .extend(b"RTSP/1.0 200 OK\r\nCSeq: 42\r\n\r\n");
        let Some(Err(e)) = core.poll_item(&streams, t0) else {
            panic!("expected error");
        };
        assert!(e.to_string().contains("Unexpected RTSP response"), "{e}");
    }

    /// Interleaved RTP packets are returned once complete; data on unassigned
    /// channels is ignored.
    #[test]
    fn interleaved_rtp() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        core.tcp_buf().extend(&interleaved(4, 1, b"unassigned"));
        let msg = interleaved(0, 0x41d4, b"\x65slice");
        let (first, second) = msg.split_at(10);
        core.tcp_buf().extend(first);
        assert!(core.poll_item(&streams, t0).is_none());
        let t1 = t0 + Duration::from_millis(5);
        core.tcp_buf().extend(second);
        match core.poll_item(&streams, t1) {
            Some(Ok(PlayingItem::Rtp(p))) => {
                assert_eq!(p.stream_id(), 0);
                assert_eq!(p.stream().media(), "video");
                assert_eq!(p.packet().meta.sequence_number, 0x41d4);
                assert_eq!(p.packet().meta.ctx.received(), t1);
                assert_eq!(p.packet().payload().to_vec(), b"\x65slice");
                assert_eq!(p.raw().to_vec(), msg[4..]);
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        assert!(core.poll_item(&streams, t1).is_none());
    }

    #[test]
    fn udp_rtp_and_rtcp() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        let write = |core: &mut PlayingCore, data: &[u8]| {
            let (s1, _) = core.udp_buf(1).spare_capacity(data.len());
            s1[..data.len()].copy_from_slice(data);
            u16::try_from(data.len()).unwrap()
        };
        let rtp = interleaved(0, 1, b"audio");
        let len = write(&mut core, &rtp[4..]);
        core.udp_received(1, ChannelType::Rtp, len, t0);
        const SR: &[u8] = b"\x80\xc8\x00\x06\xdc\xc4\xa0\xd8\
                            \xe4\x36\x2f\x99\xcc\xcc\xcc\xcc\
                            \x00\x00\x00\x00\x00\x2a\x43\x33\
                            \x2f\x4c\x34\x1d";
        let len = write(&mut core, SR);
        core.udp_received(1, ChannelType::Rtcp, len, t0);
        match core.poll_item(&streams, t0) {
            Some(Ok(PlayingItem::Rtp(p))) => {
                assert_eq!(p.stream_id(), 1);
                assert_eq!(p.packet().meta.ctx.received(), t0);
                assert_eq!(p.packet().payload().to_vec(), b"audio");
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        match core.poll_item(&streams, t0) {
            Some(Ok(PlayingItem::Rtcp(p))) => {
                assert_eq!(p.stream_id(), 1);
                assert_eq!(p.raw(), SR);
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        assert!(core.poll_item(&streams, t0).is_none());
    }

    #[test]
    fn eof() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        core.tcp_buf().extend(&interleaved(0, 1, b"\x65slice"));
        core.handle_tcp_eof();
        assert!(matches!(
            core.poll_item(&streams, t0),
            Some(Ok(PlayingItem::Rtp(_)))
        ));
        assert!(core.poll_item(&streams, t0).is_none());
        assert!(core.is_closed());
    }

    #[test]
    fn eof_mid_message() {
        let Fixture {
            mut core,
            streams,
            t0,
        } = fixture();
        core.tcp_buf()
            .extend(&interleaved(0, 1, b"\x65slice")[..10]);
        core.handle_tcp_eof();
        let Some(Err(e)) = core.poll_item(&streams, t0) else {
            panic!("expected error");
        };
        assert!(
            e.to_string().contains("Incomplete RTSP message at EOF"),
            "{e}"
        );
    }
}
