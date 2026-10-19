// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use bytes::{Buf as _, BufMut as _, BytesMut};
use futures::{Sink, Stream};
use std::time::Instant;
use tokio::io::AsyncWrite;
use tokio::net::{TcpStream, UdpSocket};
use url::Host;

use crate::buf::MarkBuf;
use crate::inputs::{Input as _, Split};
use crate::rtsp::msg::OwnedMessage;
use crate::{Error, ErrorInt, RtspMessageContext};

use super::{ConnectionContext, ReceivedMessage, WallTime};

/// Default initial capacity for the read ring buffer (64 KiB).
const DEFAULT_READ_CAPACITY: usize = 64 * 1024;

/// Buffered outgoing bytes at or above which [`Connection::poll_write_ready`]
/// applies backpressure.
///
/// This bounds how much caller-supplied media (see
/// [`Connection::queue_data`]) can pile up when the peer reads slowly, and so
/// how far behind real time it plays out: 4 KiB is about half a second of
/// G.711 (8,000 bytes per second plus headers). Below the mark, one item of
/// any size is accepted, so a single large frame (up to the 64 KiB
/// interleaved data limit) never waits forever. RTSP requests are always
/// accepted, so the buffer may exceed this briefly.
const WRITE_HIGH_WATER: usize = 4 * 1024;

/// A RTSP connection which implements `Stream`, `Sink`, and `Unpin`.
pub(crate) struct Connection {
    stream: TcpStream,
    ctx: ConnectionContext,
    parser: crate::rtsp::parse::Parser,
    read_buf: MarkBuf,

    /// Write buffer for outgoing messages, appended to by `start_send` and
    /// [`Connection::queue_data`] and drained by `poll_flush`.
    ///
    /// A `BytesMut` so that `poll_flush` can drop a partial write from the
    /// front in constant time, without moving what's left.
    write_buf: BytesMut,

    /// Total bytes written to `stream` since the connection was established.
    ///
    /// Together with `write_buf.len()`, this tells whether a particular
    /// message (such as a keepalive request) has been written, even while
    /// later messages remain buffered. See [`Connection::queued_end`].
    written: u64,

    /// Set once a write fails, to the kind of the error.
    ///
    /// `write_buf` is then cleared and all later writes fail: the remainder of
    /// a partly written message would corrupt the framing of anything sent
    /// after it.
    write_failed: Option<std::io::ErrorKind>,

    /// Tasks waiting for `write_buf` to drain, other than the one tokio will
    /// wake on writability.
    ///
    /// The session's `Stream` impl (flushing keepalives) and its `Sink` impl
    /// (flushing backchannel media) may be polled from different tasks, e.g.
    /// after `StreamExt::split`. The `TcpStream` remembers only the most
    /// recent task to see `Poll::Pending` on write, so whichever task finally
    /// drains the buffer wakes the others.
    write_waiters: Vec<std::task::Waker>,
}

impl Connection {
    pub(crate) async fn connect(
        host: Host<&str>,
        port: u16,
        max_message_size: usize,
        bind_addr: Option<std::net::IpAddr>,
    ) -> Result<Self, std::io::Error> {
        let stream = match bind_addr {
            None => match host {
                Host::Domain(h) => TcpStream::connect((h, port)).await,
                Host::Ipv4(h) => TcpStream::connect((h, port)).await,
                Host::Ipv6(h) => TcpStream::connect((h, port)).await,
            }?,
            Some(local) => Self::connect_bound(host, port, local).await?,
        };
        Self::from_stream(stream, max_message_size)
    }

    /// Connects to `host:port` from the local address `local` (port chosen by the OS).
    async fn connect_bound(
        host: Host<&str>,
        port: u16,
        local: std::net::IpAddr,
    ) -> Result<TcpStream, std::io::Error> {
        use tokio::net::{TcpSocket, lookup_host};
        let host = host.to_string();
        let mut last_err = None;
        for addr in lookup_host((host.as_str(), port)).await? {
            if addr.is_ipv4() != local.is_ipv4() {
                continue; // can only bind a source of the same address family
            }
            let sock = if addr.is_ipv4() {
                TcpSocket::new_v4()
            } else {
                TcpSocket::new_v6()
            }?;
            sock.bind(std::net::SocketAddr::new(local, 0))?;
            match sock.connect(addr).await {
                Ok(s) => return Ok(s),
                Err(e) => last_err = Some(e),
            }
        }
        Err(last_err.unwrap_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::AddrNotAvailable,
                "no resolved address matched the bind address family",
            )
        }))
    }

    pub(crate) fn from_stream(
        stream: TcpStream,
        max_message_size: usize,
    ) -> Result<Self, std::io::Error> {
        let established_wall = WallTime::now();
        let local_addr = stream.local_addr()?;
        let peer_addr = stream.peer_addr()?;
        Ok(Self {
            stream,
            ctx: ConnectionContext {
                local_addr,
                peer_addr,
                established_wall,
            },
            parser: crate::rtsp::parse::Parser::builder()
                .max_message_size(max_message_size)
                .build(),
            read_buf: MarkBuf::new(DEFAULT_READ_CAPACITY),
            write_buf: BytesMut::new(),
            written: 0,
            write_failed: None,
            write_waiters: Vec::new(),
        })
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.ctx
    }

    pub(crate) fn read_buf(&self) -> &MarkBuf {
        &self.read_buf
    }

    /// Reads body data from the ring buffer as `Bytes`.
    ///
    /// This copies the data out. Use for cold paths (RTSP responses) or the
    /// public `PacketItem` API. The `Demuxed` path reads directly from the
    /// ring buffer to avoid this copy.
    pub(crate) fn body_bytes(&self, body_pos: u64, body_len: u32) -> bytes::Bytes {
        let (s1, s2) = self.read_buf.split(body_pos, body_len as usize).slices();
        let mut buf = Vec::with_capacity(body_len as usize);
        buf.extend_from_slice(s1);
        buf.extend_from_slice(s2);
        bytes::Bytes::from(buf)
    }

    /// Returns true iff messages are queued that haven't been fully written.
    pub(crate) fn has_unflushed(&self) -> bool {
        !self.write_buf.is_empty()
    }

    pub(crate) fn eof_ctx(&self) -> RtspMessageContext {
        RtspMessageContext {
            pos: self.parser.stream_pos() + self.read_buf.unparsed_len() as u64,
            received_wall: WallTime::now(),
            received: Instant::now(),
        }
    }

    /// Returns the total bytes written so far.
    ///
    /// A message has been written once this reaches the value
    /// [`Connection::queued_end`] returned right after it was queued.
    pub(crate) fn written(&self) -> u64 {
        self.written
    }

    /// Returns the value [`Connection::written`] will have once everything
    /// queued so far has been written.
    pub(crate) fn queued_end(&self) -> u64 {
        self.written + self.write_buf.len() as u64
    }

    /// Returns an error to report if an earlier write failed.
    fn write_failed_error(&self) -> Option<ErrorInt> {
        self.write_failed.map(|kind| ErrorInt::WriteError {
            conn_ctx: self.ctx,
            source: std::io::Error::new(kind, "connection unusable after an earlier write error"),
        })
    }

    /// Records that a write failed with `source`, returning the error.
    ///
    /// Discards the write buffer, so nothing left over from a partly written
    /// message is sent later, and makes later writes fail.
    fn fail_write(&mut self, source: std::io::Error) -> ErrorInt {
        self.write_failed = Some(source.kind());
        self.write_buf = BytesMut::new();
        self.wake_write_waiters();
        ErrorInt::WriteError {
            conn_ctx: self.ctx,
            source,
        }
    }

    /// Appends an RTSP interleaved data message to the write buffer.
    ///
    /// `write_body` appends the message body to the supplied buffer. If the
    /// resulting body exceeds the 16-bit length field ([RFC 2326 section
    /// 10.12](https://datatracker.ietf.org/doc/html/rfc2326#section-10.12)),
    /// nothing is queued and this returns an error. If an earlier write
    /// failed, `write_body` isn't called and this returns an error. The caller
    /// must eventually call `poll_flush`.
    pub(crate) fn queue_data(
        &mut self,
        channel_id: u8,
        write_body: impl FnOnce(&mut BytesMut),
    ) -> Result<(), Error> {
        if let Some(e) = self.write_failed_error() {
            return Err(wrap!(e));
        }
        let start = self.write_buf.len();
        self.write_buf.extend_from_slice(&[b'$', channel_id, 0, 0]);
        write_body(&mut self.write_buf);
        let body_len = self.write_buf.len() - start - 4;
        let Ok(body_len) = u16::try_from(body_len) else {
            self.write_buf.truncate(start);
            return Err(wrap!(ErrorInt::Internal(
                format!(
                    "interleaved data body of {body_len} bytes exceeds the maximum of {}",
                    u16::MAX
                )
                .into(),
            )));
        };
        self.write_buf[start + 2..start + 4].copy_from_slice(&body_len.to_be_bytes());
        Ok(())
    }

    /// Returns `Poll::Ready` when the write buffer is below the high-water
    /// mark, flushing as necessary.
    pub(crate) fn poll_write_ready(
        &mut self,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), ErrorInt>> {
        if let Some(e) = self.write_failed_error() {
            return std::task::Poll::Ready(Err(e));
        }
        if self.write_buf.len() < WRITE_HIGH_WATER {
            return std::task::Poll::Ready(Ok(()));
        }
        match std::pin::Pin::new(&mut *self).poll_flush(cx) {
            std::task::Poll::Pending if self.write_buf.len() >= WRITE_HIGH_WATER => {
                std::task::Poll::Pending
            }
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(e)),
            _ => std::task::Poll::Ready(Ok(())),
        }
    }

    /// Notes that the current task is waiting for the write buffer to drain.
    fn add_write_waiter(&mut self, cx: &std::task::Context<'_>) {
        if !self.write_waiters.iter().any(|w| w.will_wake(cx.waker())) {
            self.write_waiters.push(cx.waker().clone());
        }
    }

    /// Wakes all tasks waiting for the write buffer to drain.
    fn wake_write_waiters(&mut self) {
        for w in self.write_waiters.drain(..) {
            w.wake();
        }
    }
}

/// Tries to decode a message from the read buffer without I/O.
///
/// Separated from `Connection` methods to avoid self-borrow issues.
///
/// When `eof` is true, the TCP stream has closed. `Incomplete` and empty
/// `Ok(None)` with leftover data are promoted to errors.
fn try_decode(
    parser: &mut crate::rtsp::parse::Parser,
    read_buf: &mut MarkBuf,
    eof: bool,
) -> Result<Option<ReceivedMessage>, CodecError> {
    use crate::rtsp::parse::FeedError;

    let pos = parser.stream_pos();
    let unparsed = read_buf.unparsed();
    let mut input = {
        let split = read_buf.unparsed_split();
        let (first, second) = split.slices();
        Split::new(first, second)
    };
    let initial_len = input.len();

    match parser.feed(&mut input) {
        Ok(None) => Ok(None), // idle, no data; caller distinguishes EOF from "need more"
        Ok(Some((msg, body_slice))) => {
            let consumed = initial_len - input.len();
            let body_len = body_slice.len();
            let body_pos = unparsed + (consumed - body_len) as u64;
            read_buf.advance_unparsed(unparsed + consumed as u64);
            Ok(Some(ReceivedMessage {
                msg,
                body_pos,
                body_len: body_len as u32,
                ctx: RtspMessageContext {
                    pos,
                    received_wall: WallTime::now(),
                    received: Instant::now(),
                },
            }))
        }
        Err(FeedError::Incomplete(_)) if !eof => {
            // On Incomplete, the parser may have stably consumed some bytes
            // (e.g. header lines). Advance past them.
            let consumed = initial_len - input.len();
            if consumed > 0 {
                read_buf.advance_unparsed(unparsed + consumed as u64);
            }
            Ok(None)
        }
        Err(FeedError::Incomplete(inc)) => {
            // EOF with incomplete data: the message is truncated.
            Err(CodecError::ParseError {
                description: format!(
                    "Incomplete RTSP message at EOF ({inc}); buffered:\n{:#?}",
                    crate::hex::LimitedHex::from_split(read_buf.unparsed_split(), 128),
                ),
                pos,
            })
        }
        Err(FeedError::Invalid(inv)) => Err(CodecError::ParseError {
            description: format!(
                "Invalid RTSP message: {inv}; buffered:\n{:#?}",
                crate::hex::LimitedHex::from_split(read_buf.unparsed_split(), 128),
            ),
            pos: inv.pos,
        }),
    }
}

/// An intermediate error type used internally.
#[derive(Debug)]
#[allow(dead_code)] // IoError reserved for future use
enum CodecError {
    IoError(std::io::Error),
    ParseError { description: String, pos: u64 },
}

impl Stream for Connection {
    type Item = Result<ReceivedMessage, Error>;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        let this = &mut *self;
        loop {
            // Try decoding from existing buffered data.
            match try_decode(&mut this.parser, &mut this.read_buf, false) {
                Ok(Some(msg)) => return std::task::Poll::Ready(Some(Ok(msg))),
                Ok(None) => {}
                Err(e) => {
                    return std::task::Poll::Ready(Some(Err(codec_err_to_error(
                        &this.ctx,
                        &this.parser,
                        &this.read_buf,
                        e,
                    ))));
                }
            }

            // Need more data. Read from the stream into the ring buffer
            // using vectored I/O to fill both halves of the ring.
            match this.stream.poll_read_ready(cx) {
                std::task::Poll::Ready(Ok(())) => {}
                std::task::Poll::Ready(Err(error)) => {
                    let pos = this.parser.stream_pos() + this.read_buf.unparsed_len() as u64;
                    return std::task::Poll::Ready(Some(Err(wrap!(ErrorInt::RtspReadError {
                        conn_ctx: this.ctx,
                        msg_ctx: RtspMessageContext {
                            pos,
                            received_wall: WallTime::now(),
                            received: Instant::now(),
                        },
                        source: error,
                    }))));
                }
                std::task::Poll::Pending => return std::task::Poll::Pending,
            }
            let (first, second) = this.read_buf.spare_capacity(4096);
            let mut bufs = [
                std::io::IoSliceMut::new(first),
                std::io::IoSliceMut::new(second),
            ];
            match this.stream.try_read_vectored(&mut bufs) {
                Ok(0) => {
                    // EOF. Try decode with eof=true.
                    return match try_decode(&mut this.parser, &mut this.read_buf, true) {
                        Ok(Some(msg)) => std::task::Poll::Ready(Some(Ok(msg))),
                        Ok(None) => std::task::Poll::Ready(None),
                        Err(e) => std::task::Poll::Ready(Some(Err(codec_err_to_error(
                            &this.ctx,
                            &this.parser,
                            &this.read_buf,
                            e,
                        )))),
                    };
                }
                Ok(n) => {
                    this.read_buf.advance_end(n);
                    // Loop to try decoding again.
                }
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    // Spurious readiness; re-register and wait.
                    continue;
                }
                Err(error) => {
                    let pos = this.parser.stream_pos() + this.read_buf.unparsed_len() as u64;
                    return std::task::Poll::Ready(Some(Err(wrap!(ErrorInt::RtspReadError {
                        conn_ctx: this.ctx,
                        msg_ctx: RtspMessageContext {
                            pos,
                            received_wall: WallTime::now(),
                            received: Instant::now(),
                        },
                        source: error,
                    }))));
                }
            }
        }
    }
}

fn codec_err_to_error(
    ctx: &ConnectionContext,
    parser: &crate::rtsp::parse::Parser,
    read_buf: &MarkBuf,
    e: CodecError,
) -> Error {
    wrap!(match e {
        CodecError::IoError(error) => ErrorInt::RtspReadError {
            conn_ctx: *ctx,
            msg_ctx: RtspMessageContext {
                pos: parser.stream_pos() + read_buf.unparsed_len() as u64,
                received_wall: WallTime::now(),
                received: Instant::now(),
            },
            source: error,
        },
        CodecError::ParseError { description, pos } => ErrorInt::RtspFramingError {
            conn_ctx: *ctx,
            msg_ctx: RtspMessageContext {
                pos,
                received_wall: WallTime::now(),
                received: Instant::now(),
            },
            description,
        },
    })
}

/// `Sink` impl for RTSP messages.
///
/// `poll_ready` is always ready: `start_send` appends to an unbounded write
/// buffer, after anything queued earlier, so internal callers may send a small
/// RTSP request without waiting for readiness. Bulk data goes through
/// [`Connection::queue_data`] and [`Connection::poll_write_ready`] instead.
///
/// Once a write fails, the connection is unusable for writing: `start_send`,
/// `poll_flush`, and `poll_close` return errors without writing anything more.
impl Sink<OwnedMessage> for Connection {
    type Error = ErrorInt;

    fn poll_ready(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        std::task::Poll::Ready(Ok(()))
    }

    /// Queues `item` after any messages not yet fully flushed.
    ///
    /// Appending rather than replacing keeps messages whole and in order when
    /// one is queued while another is still being flushed, as a receiver report
    /// may be while a keepalive request is.
    fn start_send(
        mut self: std::pin::Pin<&mut Self>,
        item: OwnedMessage,
    ) -> Result<(), Self::Error> {
        if let Some(e) = self.write_failed_error() {
            return Err(e);
        }
        item.write(&mut (&mut self.write_buf).writer())
            .expect("BytesMut Writer is infallible");
        Ok(())
    }

    fn poll_flush(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        let this = &mut *self;
        if let Some(e) = this.write_failed_error() {
            return std::task::Poll::Ready(Err(e));
        }

        // Bytes written by this call. They're removed from the front of
        // `write_buf` once, on return.
        let mut written = 0;
        while written < this.write_buf.len() {
            match std::pin::Pin::new(&mut this.stream).poll_write(cx, &this.write_buf[written..]) {
                std::task::Poll::Ready(Ok(0)) => {
                    return std::task::Poll::Ready(Err(
                        this.fail_write(std::io::ErrorKind::WriteZero.into())
                    ));
                }
                std::task::Poll::Ready(Ok(n)) => {
                    written += n;
                    this.written += n as u64;
                }
                std::task::Poll::Ready(Err(e)) => {
                    return std::task::Poll::Ready(Err(this.fail_write(e)));
                }
                std::task::Poll::Pending => {
                    this.write_buf.advance(written);
                    this.add_write_waiter(cx);
                    return std::task::Poll::Pending;
                }
            }
        }
        this.write_buf.clear();
        this.wake_write_waiters();
        match std::pin::Pin::new(&mut this.stream).poll_flush(cx) {
            std::task::Poll::Ready(Ok(())) => std::task::Poll::Ready(Ok(())),
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(this.fail_write(e))),
            std::task::Poll::Pending => std::task::Poll::Pending,
        }
    }

    fn poll_close(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        match self.as_mut().poll_flush(cx) {
            std::task::Poll::Ready(Ok(())) => {}
            other => return other,
        }
        let this = &mut *self;
        match std::pin::Pin::new(&mut this.stream).poll_shutdown(cx) {
            std::task::Poll::Ready(Ok(())) => std::task::Poll::Ready(Ok(())),
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(this.fail_write(e))),
            std::task::Poll::Pending => std::task::Poll::Pending,
        }
    }
}

/// tokio-specific version of [`crate::UdpPair`].
pub(crate) struct UdpPair {
    pub(crate) rtp_port: u16,
    pub(crate) rtp_socket: UdpSocket,
    pub(crate) rtcp_socket: UdpSocket,
}

impl UdpPair {
    pub(crate) fn for_ip(ip_addr: std::net::IpAddr) -> Result<Self, std::io::Error> {
        let inner = crate::UdpPair::for_ip(ip_addr)?;
        inner.rtp_socket.set_nonblocking(true)?;
        inner.rtcp_socket.set_nonblocking(true)?;
        Ok(Self {
            rtp_port: inner.rtp_port,
            rtp_socket: UdpSocket::from_std(inner.rtp_socket)?,
            rtcp_socket: UdpSocket::from_std(inner.rtcp_socket)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `connect` with a `bind_addr` binds the outgoing socket to that local address.
    #[tokio::test]
    async fn connect_binds_the_source() {
        use url::Host;
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let local = std::net::IpAddr::V4(std::net::Ipv4Addr::LOCALHOST);
        let (client, accepted) = tokio::join!(
            Connection::connect(
                Host::Ipv4(std::net::Ipv4Addr::LOCALHOST),
                port,
                usize::MAX,
                Some(local)
            ),
            listener.accept()
        );
        client.unwrap();
        // the server sees the bound local address as the connection's source
        assert_eq!(accepted.unwrap().1.ip(), local);
    }

    #[test]
    fn crlf_data() {
        let mut read_buf = MarkBuf::new(64);
        let data = b"\r\n$\x00\x00\x04asdfrest";
        let (first, _) = read_buf.spare_capacity(data.len());
        first[..data.len()].copy_from_slice(data);
        read_buf.advance_end(data.len());

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false)
            .unwrap()
            .unwrap();
        // Read body from ring buffer.
        let (s1, s2) = read_buf.split(msg.body_pos, msg.body_len as usize).slices();
        assert_eq!(s1, b"asdf");
        assert!(s2.is_empty());
        assert_eq!(read_buf.unparsed_len(), 4); // "rest" remains
    }

    /// Messages queued back to back before a flush, e.g. a receiver report
    /// queued while a keepalive request is still being flushed, all reach the
    /// peer whole and in order.
    #[tokio::test]
    async fn start_send_appends() {
        use crate::rtsp::msg::{self, Message};
        use futures::{SinkExt as _, StreamExt as _};

        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let (client, server) = tokio::join!(
            TcpStream::connect(listener.local_addr().unwrap()),
            listener.accept()
        );
        let mut client = Connection::from_stream(client.unwrap(), usize::MAX).unwrap();
        let mut server = Connection::from_stream(server.unwrap().0, usize::MAX).unwrap();

        client
            .start_send_unpin(OwnedMessage::Request {
                head: msg::Request {
                    method: msg::Method::GET_PARAMETER,
                    request_uri: None,
                    headers: [(
                        msg::HeaderName::CSEQ,
                        msg::HeaderValue::try_from("7").unwrap(),
                    )]
                    .into(),
                },
                body: bytes::Bytes::new(),
            })
            .unwrap();
        assert!(!client.write_buf.is_empty());
        client
            .start_send_unpin(OwnedMessage::Data {
                channel_id: 1,
                body: bytes::Bytes::from_static(b"report"),
            })
            .unwrap();
        client.flush().await.unwrap();
        assert!(client.write_buf.is_empty());

        let m = server.next().await.unwrap().unwrap();
        match m.msg {
            Message::Request(r) => {
                assert_eq!(r.method, msg::Method::GET_PARAMETER);
                assert_eq!(r.headers.get("CSeq").unwrap().to_string(), "7");
            }
            o => panic!("expected request, got {o:#?}"),
        }
        let m = server.next().await.unwrap().unwrap();
        match m.msg {
            Message::Data(d) => {
                assert_eq!(d.channel_id, 1);
                assert_eq!(&server.body_bytes(m.body_pos, m.body_len)[..], b"report");
            }
            o => panic!("expected data, got {o:#?}"),
        }
    }

    /// `queue_data` frames interleaved data and rejects bodies that don't fit
    /// the 16-bit length without queueing anything.
    #[tokio::test]
    async fn queue_data() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let client = TcpStream::connect(listener.local_addr().unwrap())
            .await
            .unwrap();
        let mut conn = Connection::from_stream(client, usize::MAX).unwrap();
        conn.queue_data(3, |out| out.extend_from_slice(b"abc"))
            .unwrap();
        let e = conn
            .queue_data(4, |out| out.resize(out.len() + 65_536, 0))
            .unwrap_err();
        assert!(e.to_string().contains("65536 bytes"), "{e}");
        conn.queue_data(5, |out| out.resize(out.len() + 65_535, 1))
            .unwrap();
        assert_eq!(&conn.write_buf[..11], b"$\x03\x00\x03abc$\x05\xff\xff");
        assert_eq!(conn.write_buf.len(), 7 + 4 + 65_535);
    }

    /// `written` counts bytes as they go out, and `queued_end` marks where
    /// the messages queued so far end.
    #[tokio::test]
    async fn written_and_queued_end() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let client = TcpStream::connect(listener.local_addr().unwrap())
            .await
            .unwrap();
        let mut conn = Connection::from_stream(client, usize::MAX).unwrap();
        assert_eq!((conn.written(), conn.queued_end()), (0, 0));
        conn.queue_data(0, |out| out.extend_from_slice(b"abc"))
            .unwrap();
        assert_eq!((conn.written(), conn.queued_end()), (0, 7));
        futures::SinkExt::<OwnedMessage>::flush(&mut conn)
            .await
            .unwrap();
        assert_eq!((conn.written(), conn.queued_end()), (7, 7));
        conn.queue_data(1, |out| out.extend_from_slice(b"de"))
            .unwrap();
        assert_eq!((conn.written(), conn.queued_end()), (7, 13));
    }

    /// Once a write fails, the rest of the buffer is discarded and later
    /// writes fail without sending anything, so the remainder of a partly
    /// written message can't corrupt a later request's framing (such as the
    /// `TEARDOWN` attempted when the session is dropped).
    #[tokio::test]
    async fn write_error_discards_buffer() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let client = TcpStream::connect(listener.local_addr().unwrap())
            .await
            .unwrap();
        let (server, _) = listener.accept().await.unwrap();
        drop(server);
        let mut conn = Connection::from_stream(client, usize::MAX).unwrap();

        // Writes to the closed peer fail once its reset arrives.
        let kind = tokio::time::timeout(std::time::Duration::from_secs(10), async {
            loop {
                conn.queue_data(0, |out| out.resize(out.len() + 1024, 0))
                    .unwrap();
                match futures::SinkExt::<OwnedMessage>::flush(&mut conn).await {
                    Ok(()) => tokio::time::sleep(std::time::Duration::from_millis(10)).await,
                    Err(ErrorInt::WriteError { source, .. }) => break source.kind(),
                    Err(e) => panic!("unexpected error: {e}"),
                }
            }
        })
        .await
        .unwrap();
        assert!(conn.write_buf.is_empty());
        let written = conn.written();

        let check = |r: Result<(), Error>| match r.as_ref().map_err(|e| &*e.0) {
            Err(ErrorInt::WriteError { source, .. }) => {
                assert_eq!(source.kind(), kind);
                assert!(
                    source.to_string().contains("earlier write error"),
                    "{source}"
                );
            }
            o => panic!("expected write error, got {o:?}"),
        };
        check(conn.queue_data(0, |_| panic!("body shouldn't be written")));
        check(
            futures::SinkExt::<OwnedMessage>::send(
                &mut conn,
                OwnedMessage::Data {
                    channel_id: 0,
                    body: bytes::Bytes::from_static(b"x"),
                },
            )
            .await
            .map_err(|e| wrap!(e)),
        );
        check(
            futures::SinkExt::<OwnedMessage>::flush(&mut conn)
                .await
                .map_err(|e| wrap!(e)),
        );
        check(
            std::future::poll_fn(|cx| conn.poll_write_ready(cx))
                .await
                .map_err(|e| wrap!(e)),
        );
        assert!(conn.write_buf.is_empty());
        assert_eq!(conn.written(), written);
    }

    #[test]
    fn response_decode() {
        let mut read_buf = MarkBuf::new(64);
        let data = b"RTSP/1.0 200 OK\r\nCSeq: 1\r\n\r\n";
        let (first, _) = read_buf.spare_capacity(data.len());
        first[..data.len()].copy_from_slice(data);
        read_buf.advance_end(data.len());

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false)
            .unwrap()
            .unwrap();
        assert!(matches!(msg.msg, crate::rtsp::msg::Message::Response(_)));
        assert_eq!(msg.body_len, 0);
        assert_eq!(read_buf.unparsed_len(), 0);
    }
}
