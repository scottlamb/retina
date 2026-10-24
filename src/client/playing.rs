// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! The sans-I/O core of a playing session; see [`PlayingCore`].

// Without the feature, only what `Session` uses is reachable.
#![cfg_attr(not(feature = "unstable-sans-io"), allow(dead_code))]

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use bytes::Bytes;
use log::{trace, warn};
use url::Url;

use super::channel_mapping::ChannelType;
use super::conn::ConnCore;
use super::parse::{self, SessionHeader};
use super::receiver_report::{ReceptionStats, ReportSchedule, ReportWriter};
use super::session_core::{SetupCore, UdpTransmit};
use super::{PlayingItem, Presentation, RtpPacket, Stream, Tool, rtp::StreamReceiver};
use crate::buf::MarkBuf;
use crate::rtp::{Pushed, Reorderer};
use crate::rtsp::msg::{self, OwnedMessage};
use crate::{
    ConnectionContext, Error, ErrorInt, PacketContext, PacketContextInner, RtspMessageContext,
    StreamContext, WallTime,
};

/// The state of a playing session; see [`super::SessionCore`].
///
/// This holds the RTSP parser and the buffers received data is read into,
/// each stream's RTP validation state, and keepalive and RTCP receiver report
/// state.
pub(crate) struct PlayingCore {
    conn: ConnCore,
    presentation: Presentation,
    sdp: Bytes,
    session: SessionHeader,

    /// Bitmask of [`super::SessionFlag`]s, for [`PlayingCore::into_setup`].
    flags: u8,

    /// State for each stream in the presentation which has been set up.
    streams: Box<[Option<PlayingStream>]>,

    /// UDP datagrams which have been received but not yet parsed, in order.
    udp_pending: VecDeque<StreamItem>,

    keepalive: Keepalive,

    /// The state of RTCP receiver reports, iff they're enabled via
    /// [`super::SessionOptions::receiver_reports`].
    reports: Option<Reports>,

    /// Receiver reports for UDP streams which have yet to be returned from
    /// `poll_transmit_udp`.
    transmit_udp: VecDeque<UdpTransmit>,
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
    pub(crate) rtp_handler: StreamReceiver,

    /// The reorder buffer, which every RTP packet passes through. On TCP, it
    /// has no delay; it just drops late packets and recognizes restarts. It
    /// also keeps sequence number statistics for receiver reports.
    pub(crate) reorderer: Reorderer<ReorderItem>,

    pub(crate) ctx: StreamContext,

    /// For a UDP stream, the buffer which datagrams are received into.
    pub(crate) udp_buf: Option<MarkBuf>,

    /// Reception statistics for RTCP receiver reports, iff they're enabled.
    pub(crate) reception: Option<ReceptionStats>,

    /// True for a stream Retina sends rather than receives (ONVIF
    /// backchannel).
    pub(crate) sending: bool,
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
pub(crate) enum KeepaliveState {
    Idle,
    /// Written once [`crate::rtsp::transmit::TransmitBuf::written`] reaches
    /// `end`.
    Flushing {
        cseq: u32,
        method: KeepaliveMethod,
        end: u64,
    },
    Waiting {
        cseq: u32,
        method: KeepaliveMethod,
    },
}

#[derive(Copy, Clone, Debug)]
pub(crate) enum KeepaliveMethod {
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

/// Logs a packet the reorderer dropped: a warning the first time each kind of
/// drop happens on a stream, then only at debug level.
fn note_dropped(stream_i: usize, seq: u16, pushed: Pushed, c: crate::rtp::ReorderCounters) {
    let first = match pushed {
        Pushed::Late => c.late == 1,
        Pushed::Duplicate => c.duplicates == 1,
        Pushed::Stray => c.strays == 1,
        _ => false,
    };
    if first {
        warn!(
            "stream {stream_i}: dropping {pushed:?} seq={seq}; further such drops \
             are logged at debug level"
        );
    } else {
        log::debug!("stream {stream_i}: dropping {pushed:?} seq={seq}; {c:?}");
    }
}

/// An RTP packet held in a [`PlayingStream::reorderer`].
pub(crate) struct ReorderItem {
    pkt_ctx: PacketContext,
    body_pos: u64,
    body_len: u16,
    payload_range: std::ops::Range<u16>,
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
    meta: crate::rtp::ReceivedPacketMeta<PacketContext>,
    body_pos: u64,
    body_len: u16,
    payload_range: std::ops::Range<u16>,

    /// The pin position from [`crate::rtp::Reordered::pin_pos`].
    pin_pos: u64,
}

impl PlayingCore {
    pub(crate) fn new(
        conn: ConnCore,
        presentation: Presentation,
        sdp: Bytes,
        session: SessionHeader,
        streams: Box<[Option<PlayingStream>]>,
        flags: u8,
        now: Instant,
    ) -> Self {
        let interval = keepalive_interval(&session);
        let reports = conn.options.receiver_reports.enabled().then(|| {
            let mut rng = rand::thread_rng();
            let schedule = ReportSchedule::new(now, &mut rng);
            Reports {
                writer: ReportWriter::random(&mut rng),
                due: schedule.next_due(),
                schedule,
            }
        });
        let keepalive = Keepalive {
            state: KeepaliveState::Idle,
            deadline: now + interval,
            interval,
            url: presentation.base_url.clone(),
            session_id: session.id.clone(),
            set_parameter_supported: false,
            get_parameter_supported: false,
        };
        Self {
            conn,
            presentation,
            sdp,
            session,
            flags,
            streams,
            udp_pending: VecDeque::new(),
            keepalive,
            reports,
            transmit_udp: VecDeque::new(),
        }
    }

    /// Returns to a [`SetupCore`] for the same session, so that it can be
    /// torn down.
    ///
    /// Any data already received stays buffered; the `TEARDOWN` ignores it.
    pub(crate) fn into_setup(self) -> SetupCore {
        SetupCore::from_playing(
            self.conn,
            self.presentation,
            self.sdp,
            self.session,
            self.flags,
        )
    }

    pub fn sdp(&self) -> &[u8] {
        &self.sdp
    }

    /// Returns the streams in the presentation.
    #[inline]
    pub fn streams(&self) -> &[Stream] {
        &self.presentation.streams
    }

    /// Returns the server's version as declared in the `DESCRIBE` response's
    /// `a:tool` SDP attribute.
    pub fn tool(&self) -> Option<&Tool> {
        self.conn.tool.as_ref()
    }

    /// Returns the buffer the caller should fill with bytes received on the
    /// RTSP connection, via `spare_capacity` and `advance_end`.
    #[inline]
    pub fn read_buf(&mut self) -> &mut MarkBuf {
        self.conn.read_buf()
    }

    /// Notes that the peer has closed the RTSP connection.
    ///
    /// Once [`PlayingCore::poll_item`] has returned the remaining items,
    /// [`PlayingCore::is_closed`] is true.
    pub fn handle_eof(&mut self) {
        self.conn.eof = true;
    }

    /// Returns true if no more items will be returned, because the peer has
    /// closed the RTSP connection.
    pub fn is_closed(&self) -> bool {
        self.conn.eof
    }

    /// Returns the buffer the caller should read a datagram for UDP stream
    /// `stream_i` into, via `spare_capacity`. Follow with
    /// [`PlayingCore::udp_received`].
    ///
    /// Panics if the stream isn't a set-up UDP stream.
    pub fn udp_buf(&mut self, stream_i: usize) -> &mut MarkBuf {
        self.streams[stream_i]
            .as_mut()
            .and_then(|s| s.udp_buf.as_mut())
            .expect("udp_buf requires a UDP stream")
    }

    /// Returns true if `stream_i` was set up with UDP transport, so its
    /// sockets should be read into [`PlayingCore::udp_buf`].
    pub fn is_udp(&self, stream_i: usize) -> bool {
        self.streams[stream_i]
            .as_ref()
            .is_some_and(|s| s.udp_buf.is_some())
    }

    /// Notes that a `len`-byte datagram was written to the start of
    /// [`PlayingCore::udp_buf`]'s spare capacity.
    ///
    /// The caller may receive several datagrams before calling
    /// [`PlayingCore::poll_item`]; they stay in the buffer until parsed.
    pub fn udp_received(
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
    pub fn conn_ctx(&self) -> &ConnectionContext {
        &self.conn.ctx
    }

    /// Returns an error for a failed read from the RTSP connection.
    pub fn read_error(&self, source: std::io::Error, now: Instant) -> Error {
        self.conn.read_error(source, now)
    }

    /// Returns an error for a failed receive on UDP stream `stream_i`.
    pub fn udp_recv_error(&self, stream_i: usize, source: std::io::Error) -> Error {
        let stream_ctx = self.streams[stream_i]
            .as_ref()
            .map(|s| s.ctx)
            .unwrap_or_else(StreamContext::dummy);
        wrap!(ErrorInt::UdpRecvError {
            conn_ctx: self.conn.ctx,
            stream_ctx,
            when: WallTime::now(),
            source,
        })
    }

    /// Parses and validates the next packet from buffered data, if any.
    ///
    /// Returns `None` when more data is needed (or, if
    /// [`PlayingCore::is_closed`], never will be). Handles keepalive
    /// responses internally.
    ///
    /// The item borrows the core, so it must be dropped before the next call.
    pub fn poll_item(&mut self, now: Instant) -> Option<Result<PlayingItem<'_>, Error>> {
        match self.poll_validated(now)? {
            Ok(v) => Some(Ok(self.item(v))),
            Err(e) => Some(Err(e)),
        }
    }

    /// The first half of [`PlayingCore::poll_item`], for drivers which return
    /// the item from within a loop.
    pub(crate) fn poll_validated(&mut self, now: Instant) -> Option<Result<ValidatedItem, Error>> {
        loop {
            match self.pop_reordered(now) {
                Err(e) => return Some(Err(e)),
                Ok(Some(v)) => return Some(Ok(v)),
                Ok(None) => {}
            }
            let item = match self.conn.reader.decode(&self.conn.ctx, self.conn.eof, now) {
                Err(e) => return Some(Err(e)),
                Ok(Some(msg)) => match msg.msg {
                    msg::Message::Data(d) => {
                        match self.handle_data(
                            &msg.ctx,
                            d.channel_id,
                            msg.body_pos,
                            d.body_len,
                            now,
                        ) {
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

    /// Returns the next due packet from any stream's reorder buffer.
    fn pop_reordered(&mut self, now: Instant) -> Result<Option<ValidatedItem>, Error> {
        for (stream_i, stream) in self.streams.iter_mut().enumerate() {
            let Some(stream) = stream else { continue };
            let buf = stream.udp_buf.as_ref().unwrap_or(self.conn.reader.buf());
            let Some(p) = stream.reorderer.pop(buf, now) else {
                continue;
            };
            if p.restarted {
                log::warn!(
                    "stream {stream_i}: sender restarted RTP sequence numbers at seq={}",
                    p.header.sequence_number()
                );
                stream.rtp_handler.receiver.restart_sequence();
            }
            let meta = stream.rtp_handler.rtp(
                &self.conn,
                &stream.ctx,
                &p.item.pkt_ctx,
                stream_i,
                &p.header,
                now,
            )?;
            return Ok(Some(ValidatedItem::Rtp(ValidatedRtp {
                stream_id: stream_i,
                meta,
                body_pos: p.item.body_pos,
                body_len: p.item.body_len,
                payload_range: p.item.payload_range,
                pin_pos: p.pin_pos,
            })));
        }
        Ok(None)
    }

    /// Builds a [`PlayingItem`] which borrows the core's buffers and streams.
    pub(crate) fn item(&self, v: ValidatedItem) -> PlayingItem<'_> {
        let rtp = match v {
            ValidatedItem::Rtcp(pkt) => return PlayingItem::Rtcp(pkt),
            ValidatedItem::Rtp(rtp) => rtp,
        };
        let buf = self.streams[rtp.stream_id]
            .as_ref()
            .and_then(|s| s.udp_buf.as_ref())
            .unwrap_or(self.conn.reader.buf());
        let pkt = crate::rtp::ReceivedPacketRef::new(
            rtp.meta,
            buf,
            rtp.body_pos + u64::from(rtp.payload_range.start),
            rtp.payload_range.end - rtp.payload_range.start,
        )
        .with_pin_pos(rtp.pin_pos);
        PlayingItem::Rtp(RtpPacket {
            stream_id: rtp.stream_id,
            stream: &self.presentation.streams[rtp.stream_id],
            pkt,
            raw_pos: rtp.body_pos,
            raw_len: rtp.body_len,
        })
    }

    /// Returns the next time [`PlayingCore::handle_timeout`] should be called.
    ///
    /// This includes when a stream's reorder buffer will give up on a missing
    /// packet; [`PlayingCore::poll_item`] then returns the packets after it.
    pub fn poll_timeout(&self) -> Instant {
        let mut t = match &self.reports {
            Some(r) => self.keepalive.deadline.min(r.due),
            None => self.keepalive.deadline,
        };
        for s in self.streams.iter().flatten() {
            if let Some(r) = s.reorderer.poll_timeout() {
                t = t.min(r);
            }
        }
        t
    }

    /// Handles the passage of time, starting a keepalive request and/or
    /// writing receiver reports if due.
    ///
    /// Returns an error if the previous keepalive hasn't been flushed or
    /// answered in time.
    pub fn handle_timeout(&mut self, now: Instant) -> Result<(), Error> {
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
                conn_ctx: self.conn.ctx,
                source: std::io::Error::new(
                    std::io::ErrorKind::TimedOut,
                    format!("Unable to write keepalive {cseq} within {interval:?}",),
                ),
            }),
            KeepaliveState::Waiting { cseq, .. } => bail!(ErrorInt::RtspReadError {
                conn_ctx: self.conn.ctx,
                msg_ctx: self.conn.reader.eof_ctx(now),
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
        let cseq = self.conn.fill_req(&mut req)?;
        trace!("sending {:?} keepalive", method);
        self.conn.queue(&req);
        let keepalive = &mut self.keepalive;
        keepalive.state = KeepaliveState::Flushing {
            cseq,
            method,
            end: self.conn.transmit.queued_end(),
        };
        keepalive.deadline = now + interval;
        Ok(())
    }

    /// Writes a receiver report for each stream, which are due, and schedules
    /// the next.
    ///
    /// Each stream is its own RTP session, so each gets its own report on its
    /// own RTCP channel or socket. Over TCP, the report is queued for
    /// [`PlayingCore::transmit_buf`] (after any keepalive). Over UDP, it's
    /// queued for [`PlayingCore::poll_transmit_udp`].
    fn send_reports(&mut self, now: Instant) {
        let reports = self.reports.as_mut().expect("reports are enabled");
        for (i, s) in self.streams.iter_mut().enumerate() {
            let Some(PlayingStream {
                ctx,
                udp_buf,
                reception: Some(reception),
                reorderer,
                rtp_handler,
                ..
            }) = s
            else {
                continue;
            };
            let block = rtp_handler.receiver.ssrc().and_then(|ssrc| {
                let seq = reorderer.reception_report()?;
                Some(reception.report_block(now, ssrc, seq))
            });
            trace!("sending RTCP receiver report for stream {i}: {block:?}");
            let pkt = reports.writer.write(block.as_ref());
            match (udp_buf, &ctx.0) {
                (Some(_), _) => self.transmit_udp.push_back(UdpTransmit {
                    stream_i: i,
                    channel_type: ChannelType::Rtcp,
                    data: pkt,
                }),
                (None, crate::StreamContextInner::Tcp(tcp)) => {
                    self.conn.queue(&OwnedMessage::Data {
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

    /// Returns the bytes to write to the RTSP connection, in order.
    ///
    /// The first slice is empty iff there's nothing to write. After writing,
    /// call [`PlayingCore::advance_transmit`].
    pub fn transmit_buf(&self) -> (&[u8], &[u8]) {
        self.conn.transmit_buf()
    }

    /// Notes that the first `n` bytes of [`PlayingCore::transmit_buf`] have
    /// been written.
    ///
    /// # Panics
    ///
    /// If `n` exceeds the bytes available.
    pub fn advance_transmit(&mut self, n: usize) {
        self.conn.advance_transmit(n);
        if let KeepaliveState::Flushing { cseq, method, end } = self.keepalive.state
            && self.conn.transmit.written() >= end
        {
            self.keepalive.state = KeepaliveState::Waiting { cseq, method };
        }
    }

    /// Returns a receiver report to send on a UDP stream's RTCP socket, if any.
    ///
    /// The caller should send it right away if the socket has room and
    /// otherwise drop it, as later reports carry cumulative statistics anyway.
    pub fn poll_transmit_udp(&mut self) -> Option<UdpTransmit> {
        self.transmit_udp.pop_front()
    }

    /// Moves the keepalive deadline; follow by resetting the driver's timer.
    #[cfg(all(test, feature = "tokio"))]
    pub(crate) fn set_keepalive_deadline(&mut self, deadline: Instant) {
        self.keepalive.deadline = deadline;
    }

    /// Pretends an `OPTIONS` response advertised `GET_PARAMETER` and
    /// `SET_PARAMETER`.
    #[cfg(all(test, feature = "tokio"))]
    pub(crate) fn set_parameter_methods_supported(&mut self) {
        self.keepalive.get_parameter_supported = true;
        self.keepalive.set_parameter_supported = true;
    }

    /// Returns the state of the current keepalive request.
    #[cfg(all(test, feature = "tokio"))]
    pub(crate) fn keepalive_state(&self) -> KeepaliveState {
        self.keepalive.state
    }

    /// Returns the receiver report state, iff reports are enabled. Follow a
    /// change to `due` by resetting the driver's timer.
    #[cfg(all(test, feature = "tokio"))]
    pub(crate) fn reports_mut(&mut self) -> Option<&mut Reports> {
        self.reports.as_mut()
    }

    /// Returns true if any stream keeps reception statistics.
    #[cfg(all(test, feature = "tokio"))]
    pub(crate) fn has_reception_stats(&self) -> bool {
        self.streams
            .iter()
            .any(|s| s.as_ref().is_some_and(|s| s.reception.is_some()))
    }

    /// Returns the interleaved RTP channel id of sending stream `stream_i`.
    #[cfg(feature = "unstable-send")]
    fn sending_channel(&self, stream_i: usize) -> Result<u8, Error> {
        let Some(stream) = self.presentation.streams.get(stream_i) else {
            bail!(ErrorInt::InvalidArgument(format!(
                "can't send on stream {stream_i}: presentation has only {} streams",
                self.presentation.streams.len()
            )));
        };
        if stream.direction != super::StreamDirection::Sending {
            bail!(ErrorInt::InvalidArgument(format!(
                "can't send on stream {stream_i}: it isn't an ONVIF backchannel (a=sendonly) stream"
            )));
        }
        let Some(PlayingStream { ctx, .. }) = self.streams[stream_i].as_ref() else {
            bail!(ErrorInt::FailedPrecondition(format!(
                "can't send on stream {stream_i}: it wasn't set up before PLAY"
            )));
        };
        let crate::StreamContextInner::Tcp(crate::TcpStreamContext { rtp_channel_id }) = ctx.0
        else {
            bail!(ErrorInt::Internal(
                "sending stream unexpectedly isn't using TCP".into()
            ));
        };
        Ok(rtp_channel_id)
    }

    /// Queues an RTP packet on sending stream `stream_i`'s interleaved
    /// channel, for [`PlayingCore::transmit_buf`].
    ///
    /// On error, nothing is queued, and the session is still usable.
    #[cfg(feature = "unstable-send")]
    pub fn queue_rtp(
        &mut self,
        stream_i: usize,
        pkt: &crate::rtp::OutgoingPacketRef<'_>,
    ) -> Result<(), Error> {
        let channel_id = self.sending_channel(stream_i)?;
        let header = pkt.header();
        let mut data = Vec::with_capacity(1 + pkt.data().len());
        data.push(&header.as_bytes()[..]);
        data.extend_from_slice(pkt.data());
        // `rtp::Sender::packet` ensures the packet fits.
        self.conn.queue_data(channel_id, &data);
        Ok(())
    }

    /// Queues an RTCP packet on sending stream `stream_i`'s interleaved
    /// channel, for [`PlayingCore::transmit_buf`].
    ///
    /// On error, nothing is queued, and the session is still usable.
    #[cfg(feature = "unstable-send")]
    pub fn queue_rtcp(&mut self, stream_i: usize, pkt: &[u8]) -> Result<(), Error> {
        let channel_id = self.sending_channel(stream_i)?;
        if pkt.len() > usize::from(u16::MAX) {
            bail!(ErrorInt::InvalidArgument(format!(
                "can't send {}-byte RTCP packet on stream {stream_i}: RTSP interleaved data \
                 allows at most 65535 bytes",
                pkt.len()
            )));
        }
        self.conn.queue_data(channel_id.wrapping_add(1), &[pkt]);
        Ok(())
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
            conn_ctx: self.conn.ctx,
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
        now: Instant,
    ) -> Result<Option<StreamItem>, Error> {
        let Some(m) = self.conn.channels.lookup(channel_id) else {
            let body = self.conn.reader.body_bytes(body_pos, u32::from(body_len));
            super::handle_unassigned_data(&mut self.conn, *msg_ctx, channel_id, body, now)?;
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
        let buf = stream.udp_buf.as_ref().unwrap_or(self.conn.reader.buf());
        match item.channel_type {
            ChannelType::Rtp if stream.sending => {
                // Retina sends RTP on this stream; the server shouldn't.
                log::debug!(
                    "ignoring RTP packet received on sending stream {}",
                    item.stream_i
                );
                Ok(None)
            }
            ChannelType::Rtp => {
                let split = buf.split(item.body_pos, usize::from(item.body_len));
                let (header, payload_range) =
                    crate::rtp::PacketHeader::validate(split).map_err(|reason| {
                        wrap!(ErrorInt::PacketError {
                            conn_ctx: self.conn.ctx,
                            stream_ctx: stream.ctx,
                            pkt_ctx: item.pkt_ctx,
                            stream_id: item.stream_i,
                            description: stream.rtp_handler.validate_error(reason, split),
                        })
                    })?;

                if super::rtp::skip(&header) {
                    return Ok(None);
                }
                let seq = header.sequence_number();
                let rtp_timestamp = header.timestamp();
                let pushed = stream.reorderer.push(
                    buf,
                    header,
                    item.body_pos,
                    now,
                    ReorderItem {
                        pkt_ctx: item.pkt_ctx,
                        body_pos: item.body_pos,
                        body_len: item.body_len,
                        payload_range,
                    },
                );

                // Note the arrival for receiver reports' jitter, if the
                // reorderer's statistics counted it.
                if let Some(reception) = &mut stream.reception
                    && stream.reorderer.last_arrival_counted()
                {
                    reception.rtp(rtp_timestamp, now);
                }
                if pushed != Pushed::Held {
                    note_dropped(item.stream_i, seq, pushed, stream.reorderer.counters());
                }
                Ok(None) // returned later via `pop_reordered`.
            }
            ChannelType::Rtcp => {
                let body = Bytes::from(
                    buf.split(item.body_pos, usize::from(item.body_len))
                        .to_vec(),
                );
                match stream.rtp_handler.rtcp(
                    &self.conn,
                    &stream.ctx,
                    &item.pkt_ctx,
                    item.stream_i,
                    body,
                    now,
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
                        conn_ctx: self.conn.ctx,
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
    use crate::client::{SessionOptions, UnknownRtcpSsrcPolicy};

    const INTERVAL: Duration = Duration::from_secs(30);

    /// A core for the Reolink presentation, with its video stream (0) set up
    /// via TCP on channels 0–1 and its audio stream (1) via UDP.
    struct Fixture {
        core: PlayingCore,
        t0: Instant,
    }

    fn fixture() -> Fixture {
        fixture_with(SessionOptions::default(), true)
    }

    /// As [`fixture`], but with the given options, and with the audio stream
    /// set up via TCP on channels 2–3 unless `audio_udp`.
    fn fixture_with(options: SessionOptions, audio_udp: bool) -> Fixture {
        crate::testutil::init_logging();
        let (resp, body) =
            crate::testutil::response(include_bytes!("testdata/reolink_describe.txt"));
        let url = Url::parse("rtsp://192.168.5.206:554/h264Preview_01_main").unwrap();
        let presentation = parse::parse_describe(url, &resp, &body, false).unwrap();
        let mut conn = ConnCore::new(ConnectionContext::dummy(), options);
        conn.channels.assign(0, 0).unwrap();
        if !audio_udp {
            conn.channels.assign(2, 1).unwrap();
        }
        for _ in 1..5 {
            conn.fill_req(&mut OwnedMessage::Request {
                head: msg::Request {
                    method: msg::Method::OPTIONS,
                    request_uri: None,
                    headers: Default::default(),
                },
                body: Bytes::new(),
            })
            .unwrap();
        }
        let new_stream = |s: &Stream, udp: bool| {
            Some(PlayingStream {
                rtp_handler: StreamReceiver::new(
                    crate::rtp::Receiver::new(
                        s.clock_rate_hz(),
                        crate::rtp::ReceiverOptions::default(),
                    )
                    .unwrap(),
                    UnknownRtcpSsrcPolicy::Default,
                ),
                reorderer: Reorderer::new(
                    crate::rtp::ReorderOptions::default().max_delay(Duration::ZERO),
                ),
                ctx: StreamContext::dummy(),
                udp_buf: udp.then(|| MarkBuf::new(65536)),
                reception: None,
                sending: false,
            })
        };
        let streams = [
            new_stream(&presentation.streams[0], false),
            new_stream(&presentation.streams[1], audio_udp),
        ];
        let t0 = Instant::now();
        let core = PlayingCore::new(
            conn,
            presentation,
            Bytes::new(),
            SessionHeader {
                id: msg::HeaderValue::try_from("F8F8E425").unwrap(),
                timeout_sec: 60,
            },
            streams.into(),
            0,
            t0,
        );
        Fixture { core, t0 }
    }

    /// Returns the bytes not yet written, which must be non-empty.
    fn transmitted(core: &PlayingCore) -> String {
        let (a, b) = core.transmit_buf();
        assert!(!a.is_empty(), "should transmit");
        String::from_utf8([a, b].concat()).unwrap()
    }

    /// Writes all bytes from [`PlayingCore::transmit_buf`].
    fn flush(core: &mut PlayingCore) {
        let (a, b) = core.transmit_buf();
        core.advance_transmit(a.len() + b.len());
    }

    /// Returns an interleaved data message holding an RTP packet.
    fn interleaved(channel_id: u8, sequence_number: u16, payload: &[u8]) -> Vec<u8> {
        interleaved_with_mark(channel_id, sequence_number, true, payload)
    }

    fn interleaved_with_mark(
        channel_id: u8,
        sequence_number: u16,
        mark: bool,
        payload: &[u8],
    ) -> Vec<u8> {
        let pkt = crate::rtp::build_raw_rtp(
            sequence_number,
            0,
            96,
            0xdcc4a0d8,
            mark,
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
        let Fixture { mut core, t0 } = fixture();
        assert_eq!(core.poll_timeout(), t0 + INTERVAL);

        // Nothing is sent before the deadline.
        core.handle_timeout(t0 + INTERVAL - Duration::from_millis(1))
            .unwrap();
        assert!(core.transmit_buf().0.is_empty());

        // At the deadline, an `OPTIONS` goes out, and the next deadline is set.
        let t1 = t0 + INTERVAL;
        core.handle_timeout(t1).unwrap();
        let req = transmitted(&core);
        assert!(
            req.starts_with("OPTIONS rtsp://192.168.5.206/h264Preview_01_main/ RTSP/1.0\r\n"),
            "{req}"
        );
        assert!(req.contains("\r\nCSeq: 5\r\n"), "{req}");
        assert!(req.contains("\r\nSession: F8F8E425\r\n"), "{req}");
        assert_eq!(core.poll_timeout(), t1 + INTERVAL);
        flush(&mut core);

        // The response advertises `SET_PARAMETER`; it's used from then on.
        core.read_buf().extend(
            b"RTSP/1.0 200 OK\r\nCSeq: 5\r\n\
              Public: OPTIONS, DESCRIBE, SETUP, PLAY, TEARDOWN, SET_PARAMETER\r\n\r\n",
        );
        assert!(core.poll_item(t1).is_none());
        let t2 = t1 + INTERVAL;
        core.handle_timeout(t2).unwrap();
        let req = transmitted(&core);
        assert!(req.starts_with("SET_PARAMETER "), "{req}");
        assert!(req.contains("\r\nCSeq: 6\r\n"), "{req}");
    }

    /// A failed keepalive is only logged, and doesn't change the method.
    #[test]
    fn keepalive_error_response() {
        let Fixture { mut core, t0 } = fixture();
        let t1 = t0 + INTERVAL;
        core.handle_timeout(t1).unwrap();
        assert!(transmitted(&core).starts_with("OPTIONS "));
        flush(&mut core);
        core.read_buf()
            .extend(b"RTSP/1.0 454 Session Not Found\r\nCSeq: 5\r\n\r\n");
        assert!(core.poll_item(t1).is_none());
        core.handle_timeout(t1 + INTERVAL).unwrap();
        assert!(transmitted(&core).starts_with("OPTIONS "));
    }

    #[test]
    fn keepalive_unanswered() {
        let Fixture { mut core, t0, .. } = fixture();
        core.handle_timeout(t0 + INTERVAL).unwrap();
        transmitted(&core);
        flush(&mut core);
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
        transmitted(&core);
        let e = core.handle_timeout(t0 + 2 * INTERVAL).unwrap_err();
        assert!(
            e.to_string()
                .contains("Unable to write keepalive 5 within 30s"),
            "{e}"
        );
    }

    /// The keepalive is written once its last byte is, even if a partial
    /// write left it short or more bytes are queued after it.
    #[test]
    fn keepalive_written_precisely() {
        let Fixture { mut core, t0, .. } = fixture();
        core.handle_timeout(t0 + INTERVAL).unwrap();
        let len = transmitted(&core).len();
        core.conn.queue(&OwnedMessage::Data {
            channel_id: 1,
            body: Bytes::from_static(b"rtcp"),
        });
        core.advance_transmit(len - 1);
        assert!(matches!(
            core.keepalive.state,
            KeepaliveState::Flushing { .. }
        ));
        core.advance_transmit(1);
        assert!(matches!(
            core.keepalive.state,
            KeepaliveState::Waiting { .. }
        ));
        assert_eq!(transmitted(&core), "$\x01\x00\x04rtcp");
    }

    #[test]
    fn unexpected_response() {
        let Fixture { mut core, t0 } = fixture();
        core.read_buf()
            .extend(b"RTSP/1.0 200 OK\r\nCSeq: 42\r\n\r\n");
        let Some(Err(e)) = core.poll_item(t0) else {
            panic!("expected error");
        };
        assert!(e.to_string().contains("Unexpected RTSP response"), "{e}");
    }

    /// Interleaved RTP packets are returned once complete; data on unassigned
    /// channels is ignored.
    #[test]
    fn interleaved_rtp() {
        let Fixture { mut core, t0 } = fixture();
        core.read_buf().extend(&interleaved(4, 1, b"unassigned"));
        let msg = interleaved(0, 0x41d4, b"\x65slice");
        let (first, second) = msg.split_at(10);
        core.read_buf().extend(first);
        assert!(core.poll_item(t0).is_none());
        let t1 = t0 + Duration::from_millis(5);
        core.read_buf().extend(second);
        match core.poll_item(t1) {
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
        assert!(core.poll_item(t1).is_none());
    }

    /// Over TCP, a late packet is dropped rather than failing the session, and
    /// a sender restarting its sequence numbers shows up as a discontinuity.
    #[test]
    fn tcp_late_and_restart() {
        use crate::rtp::Continuity;
        let Fixture { mut core, t0 } = fixture();
        for seq in [1000, 1001, 1003, 1002, 10, 11] {
            core.read_buf().extend(&interleaved(0, seq, b"x"));
        }
        let items: Vec<_> = std::iter::from_fn(|| match core.poll_item(t0)? {
            Ok(PlayingItem::Rtp(p)) => {
                Some((p.packet().meta.sequence_number, p.packet().meta.continuity))
            }
            o => panic!("unexpected item: {o:#?}"),
        })
        .collect();
        assert_eq!(
            items,
            [
                (1000, Continuity::Contiguous),
                (1001, Continuity::Contiguous),
                (1003, Continuity::from_loss(1)),
                // 1002 is late; 10 is a stray.
                (11, Continuity::Discontinuity),
            ]
        );
        let counters = core.streams[0].as_ref().unwrap().reorderer.counters();
        assert_eq!(
            (counters.late, counters.strays, counters.restarts),
            (1, 1, 1)
        );
    }

    /// Over TCP, a video stream with a small frame in progress goes quiet
    /// while audio keeps arriving on the same connection. The shared buffer
    /// stays bounded, and the video depacketizer reports the eviction.
    #[cfg(feature = "h264")]
    #[test]
    fn tcp_stalled_stream_evicted() {
        use crate::codec::events::testutil::{Event, Recorder};
        use crate::codec::{Accumulate, LossReason};
        let Fixture { mut core, t0 } = fixture_with(
            SessionOptions::default().max_retained_bytes(16 << 10),
            false,
        );
        let mut video = core.streams()[0].new_depacketizer().unwrap();
        let crate::codec::Depacketizer::Video(video) = &mut video else {
            panic!("expected video");
        };
        let mut h = Recorder::new(Accumulate::Yes);
        let mut push_video = |core: &mut PlayingCore, msg: &[u8], h: &mut Recorder| {
            core.read_buf().extend(msg);
            match core.poll_item(t0) {
                Some(Ok(PlayingItem::Rtp(p))) => {
                    assert_eq!(p.stream_id(), 0);
                    video.push(p.packet(), h);
                }
                o => panic!("unexpected item: {o:#?}"),
            }
        };
        push_video(
            &mut core,
            &interleaved_with_mark(0, 1, false, b"\x7c\x85start"),
            &mut h,
        );
        h.take();
        for seq in 0..1000 {
            core.read_buf().extend(&interleaved(2, seq, &[0; 1000]));
            match core.poll_item(t0) {
                Some(Ok(PlayingItem::Rtp(p))) => assert_eq!(p.stream_id(), 1),
                o => panic!("unexpected item: {o:#?}"),
            }
        }
        assert!(
            core.conn.reader.buf().capacity() <= 64 << 10,
            "{}",
            core.conn.reader.buf().capacity()
        );
        push_video(&mut core, &interleaved(0, 2, b"\x7c\x45end"), &mut h);
        assert_eq!(h.take(), vec![Event::Loss(LossReason::Evicted)]);
    }

    #[test]
    fn udp_rtp_and_rtcp() {
        let Fixture { mut core, t0 } = fixture();
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
        match core.poll_item(t0) {
            Some(Ok(PlayingItem::Rtp(p))) => {
                assert_eq!(p.stream_id(), 1);
                assert_eq!(p.packet().meta.ctx.received(), t0);
                assert_eq!(p.packet().payload().to_vec(), b"audio");
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        match core.poll_item(t0) {
            Some(Ok(PlayingItem::Rtcp(p))) => {
                assert_eq!(p.stream_id(), 1);
                assert_eq!(p.raw(), SR);
            }
            o => panic!("unexpected item: {o:#?}"),
        }
        assert!(core.poll_item(t0).is_none());
    }

    #[test]
    fn udp_reorder() {
        let Fixture { mut core, t0 } = fixture();
        core.streams[1].as_mut().unwrap().reorderer =
            Reorderer::new(crate::rtp::ReorderOptions::default());
        let receive = |core: &mut PlayingCore, seq: u16, now: Instant| {
            let payload = format!("pkt {seq}");
            let data = &interleaved(0, seq, payload.as_bytes())[4..];
            let (s1, _) = core.udp_buf(1).spare_capacity(data.len());
            s1[..data.len()].copy_from_slice(data);
            core.udp_received(1, ChannelType::Rtp, u16::try_from(data.len()).unwrap(), now);
        };
        let poll = |core: &mut PlayingCore, now: Instant| -> Vec<String> {
            std::iter::from_fn(|| match core.poll_item(now)? {
                Ok(PlayingItem::Rtp(p)) => {
                    Some(String::from_utf8(p.packet().payload().to_vec()).unwrap())
                }
                o => panic!("unexpected item: {o:#?}"),
            })
            .collect()
        };

        // The first packets wait in case of earlier ones.
        receive(&mut core, 2, t0);
        receive(&mut core, 1, t0);
        assert_eq!(poll(&mut core, t0), Vec::<String>::new());
        let t1 = t0 + Duration::from_millis(50);
        assert_eq!(core.poll_timeout(), t1);
        assert_eq!(poll(&mut core, t1), ["pkt 1", "pkt 2"]);

        // Then a gap waits for the missing packet.
        receive(&mut core, 4, t1);
        assert_eq!(poll(&mut core, t1), Vec::<String>::new());
        receive(&mut core, 3, t1);
        assert_eq!(poll(&mut core, t1), ["pkt 3", "pkt 4"]);

        // ...or until the deadline.
        receive(&mut core, 6, t1);
        assert_eq!(poll(&mut core, t1), Vec::<String>::new());
        let t2 = t1 + Duration::from_millis(50);
        assert_eq!(core.poll_timeout(), t2);
        assert_eq!(poll(&mut core, t2), ["pkt 6"]);
        receive(&mut core, 5, t2);
        assert_eq!(poll(&mut core, t2), Vec::<String>::new());
    }

    #[test]
    fn eof() {
        let Fixture { mut core, t0 } = fixture();
        core.read_buf().extend(&interleaved(0, 1, b"\x65slice"));
        core.handle_eof();
        assert!(matches!(core.poll_item(t0), Some(Ok(PlayingItem::Rtp(_)))));
        assert!(core.poll_item(t0).is_none());
        assert!(core.is_closed());
    }

    #[test]
    fn eof_mid_message() {
        let Fixture { mut core, t0 } = fixture();
        core.read_buf()
            .extend(&interleaved(0, 1, b"\x65slice")[..10]);
        core.handle_eof();
        let Some(Err(e)) = core.poll_item(t0) else {
            panic!("expected error");
        };
        assert!(
            e.to_string().contains("Incomplete RTSP message at EOF"),
            "{e}"
        );
    }
}
