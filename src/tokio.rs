// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use bytes::{Buf as _, BufMut as _, BytesMut};
use futures::{Sink, Stream};
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Instant;
use tokio::io::AsyncWrite;
use tokio::net::{TcpStream, UdpSocket};
use url::Host;

use crate::buf::MarkBuf;
use crate::rtsp::msg::OwnedMessage;
use crate::rtsp::reader::Reader;
use crate::{Error, ErrorInt, RtspMessageContext};

use super::{ConnectionContext, ReceivedMessage, WallTime};

/// Buffered outgoing bytes at or above which [`Connection::poll_write_ready`]
/// applies backpressure.
///
/// This bounds how much caller-supplied media (such as ONVIF backchannel
/// audio, queued via [`Connection::queue_write`]) can pile up when the peer
/// reads slowly, and so how far behind real time it plays out: 4 KiB is about
/// half a second of G.711 (8,000 bytes per second plus headers). Below the
/// mark, one item of any size is accepted, so a single large frame (up to the
/// 64 KiB interleaved data limit) never waits forever. RTSP requests are
/// always accepted, so the buffer may exceed this briefly.
const WRITE_HIGH_WATER: usize = 4 * 1024;

/// The byte stream under a [`Connection`].
///
/// An enum rather than a type parameter so `Connection` and `Session` stay
/// monomorphic. Tests add an in-memory variant; see the testing notes in
/// `CONTRIBUTING.md`.
enum Transport {
    Tcp(TcpStream),

    /// An in-memory stream, for tests under paused time.
    ///
    /// A write wakes the reader directly, so the runtime never looks idle
    /// between one side's write and the other's read, as it may with loopback
    /// TCP while the kernel delivers the data.
    #[cfg(test)]
    Duplex(tokio::io::DuplexStream),
}

impl Transport {
    /// Reads into `bufs`, returning the number of bytes read; 0 means EOF.
    fn poll_read_vectored(
        &mut self,
        cx: &mut Context<'_>,
        bufs: &mut [std::io::IoSliceMut<'_>],
    ) -> Poll<std::io::Result<usize>> {
        match self {
            Transport::Tcp(s) => loop {
                std::task::ready!(s.poll_read_ready(cx))?;
                match s.try_read_vectored(bufs) {
                    // Spurious readiness; re-register and wait.
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => continue,
                    r => return Poll::Ready(r),
                }
            },
            #[cfg(test)]
            Transport::Duplex(s) => {
                // `DuplexStream` has no vectored read; fill the first nonempty
                // slice. The caller loops for more.
                let Some(buf) = bufs.iter_mut().find(|b| !b.is_empty()) else {
                    return Poll::Ready(Ok(0));
                };
                let mut buf = tokio::io::ReadBuf::new(&mut buf[..]);
                std::task::ready!(tokio::io::AsyncRead::poll_read(Pin::new(s), cx, &mut buf))?;
                Poll::Ready(Ok(buf.filled().len()))
            }
        }
    }
}

impl AsyncWrite for Transport {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buf: &[u8],
    ) -> Poll<std::io::Result<usize>> {
        match self.get_mut() {
            Transport::Tcp(s) => Pin::new(s).poll_write(cx, buf),
            #[cfg(test)]
            Transport::Duplex(s) => Pin::new(s).poll_write(cx, buf),
        }
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        match self.get_mut() {
            Transport::Tcp(s) => Pin::new(s).poll_flush(cx),
            #[cfg(test)]
            Transport::Duplex(s) => Pin::new(s).poll_flush(cx),
        }
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<std::io::Result<()>> {
        match self.get_mut() {
            Transport::Tcp(s) => Pin::new(s).poll_shutdown(cx),
            #[cfg(test)]
            Transport::Duplex(s) => Pin::new(s).poll_shutdown(cx),
        }
    }
}

/// A RTSP connection which implements `Stream`, `Sink`, and `Unpin`.
pub(crate) struct Connection {
    stream: Transport,
    ctx: ConnectionContext,

    /// The reader, which is lent out while playing; see [`Connection::take_reader`].
    reader: Option<Reader>,

    /// Write buffer for outgoing messages, appended to by `start_send` and
    /// [`Connection::queue_write`] and drained by `poll_flush`.
    ///
    /// A `BytesMut` so that `poll_flush` can drop a partial write from the
    /// front in constant time, without moving what's left.
    write_buf: BytesMut,

    /// Total bytes written to `stream` since the connection was established.
    ///
    /// This tells a [`crate::client::playing::PlayingCore`] how many of the
    /// bytes it supplied have been written, so it knows when a particular
    /// message (such as a keepalive request) is out, even while later
    /// messages remain buffered.
    written: u64,

    /// Set once a write fails, to the kind of the error.
    ///
    /// `write_buf` is then cleared and all later writes fail: the remainder of
    /// a partly written message would corrupt the framing of anything sent
    /// after it.
    write_failed: Option<std::io::ErrorKind>,
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
        let local_addr = stream.local_addr()?;
        let peer_addr = stream.peer_addr()?;
        Ok(Self::new(
            Transport::Tcp(stream),
            local_addr,
            peer_addr,
            max_message_size,
        ))
    }

    /// Wraps an in-memory stream from [`tokio::io::duplex`], for tests.
    ///
    /// There's no socket to ask for addresses, so the caller supplies them.
    #[cfg(test)]
    pub(crate) fn from_duplex(
        stream: tokio::io::DuplexStream,
        local_addr: std::net::SocketAddr,
        peer_addr: std::net::SocketAddr,
        max_message_size: usize,
    ) -> Self {
        Self::new(
            Transport::Duplex(stream),
            local_addr,
            peer_addr,
            max_message_size,
        )
    }

    fn new(
        stream: Transport,
        local_addr: std::net::SocketAddr,
        peer_addr: std::net::SocketAddr,
        max_message_size: usize,
    ) -> Self {
        Self {
            stream,
            ctx: ConnectionContext {
                local_addr,
                peer_addr,
                established_wall: WallTime::now(),
            },
            reader: Some(Reader::new(max_message_size)),
            write_buf: BytesMut::new(),
            written: 0,
            write_failed: None,
        }
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.ctx
    }

    fn reader(&self) -> &Reader {
        self.reader
            .as_ref()
            .expect("reader should be present except while playing")
    }

    /// Takes the reader, so that a [`crate::client::playing::PlayingCore`]
    /// can parse messages without going through this connection's `Stream`
    /// impl. Put it back with [`Connection::restore_reader`] before polling
    /// the `Stream` impl again.
    pub(crate) fn take_reader(&mut self) -> Reader {
        self.reader
            .take()
            .expect("reader should be present except while playing")
    }

    pub(crate) fn restore_reader(&mut self, reader: Reader) {
        assert!(self.reader.is_none());
        self.reader = Some(reader);
    }

    /// Reads body data from the ring buffer as `Bytes`; see [`Reader::body_bytes`].
    pub(crate) fn body_bytes(&self, body_pos: u64, body_len: u32) -> bytes::Bytes {
        self.reader().body_bytes(body_pos, body_len)
    }

    /// Returns true iff messages are queued that haven't been fully written.
    pub(crate) fn has_unflushed(&self) -> bool {
        !self.write_buf.is_empty()
    }

    pub(crate) fn eof_ctx(&self) -> RtspMessageContext {
        self.reader().eof_ctx(Instant::now())
    }

    /// Reads available bytes from the connection into `buf`, returning the
    /// number read. `Ready(Ok(0))` means the peer closed the connection.
    pub(crate) fn poll_read(
        &mut self,
        cx: &mut Context<'_>,
        buf: &mut MarkBuf,
    ) -> Poll<std::io::Result<usize>> {
        poll_read(&mut self.stream, cx, buf)
    }

    /// Queues `data` to be written by [`Sink::poll_flush`].
    ///
    /// If an earlier write failed, `data` is discarded; `poll_flush` returns
    /// the error.
    pub(crate) fn queue_write(&mut self, data: &[u8]) {
        if self.write_failed.is_none() {
            self.write_buf.extend_from_slice(data);
        }
    }

    /// Returns the total bytes written so far.
    pub(crate) fn written(&self) -> u64 {
        self.written
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
        ErrorInt::WriteError {
            conn_ctx: self.ctx,
            source,
        }
    }

    /// Returns `Poll::Ready` when the write buffer is below the high-water
    /// mark, flushing as necessary.
    pub(crate) fn poll_write_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), ErrorInt>> {
        if let Some(e) = self.write_failed_error() {
            return Poll::Ready(Err(e));
        }
        if self.write_buf.len() < WRITE_HIGH_WATER {
            return Poll::Ready(Ok(()));
        }
        match std::pin::Pin::new(&mut *self).poll_flush(cx) {
            Poll::Pending if self.write_buf.len() >= WRITE_HIGH_WATER => Poll::Pending,
            Poll::Ready(Err(e)) => Poll::Ready(Err(e)),
            _ => Poll::Ready(Ok(())),
        }
    }
}

/// Reads available bytes from `stream` into `buf`'s spare capacity via
/// vectored I/O, filling both halves of the ring.
fn poll_read(
    stream: &mut Transport,
    cx: &mut Context<'_>,
    buf: &mut MarkBuf,
) -> Poll<std::io::Result<usize>> {
    let (first, second) = buf.spare_capacity(4096);
    let mut bufs = [
        std::io::IoSliceMut::new(first),
        std::io::IoSliceMut::new(second),
    ];
    let n = std::task::ready!(stream.poll_read_vectored(cx, &mut bufs))?;
    buf.advance_end(n);
    Poll::Ready(Ok(n))
}

impl Stream for Connection {
    type Item = Result<ReceivedMessage, Error>;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = &mut *self;
        let reader = this
            .reader
            .as_mut()
            .expect("reader should be present except while playing");
        loop {
            // Try decoding from existing buffered data.
            match reader.decode(&this.ctx, false, Instant::now()) {
                Ok(Some(msg)) => return Poll::Ready(Some(Ok(msg))),
                Ok(None) => {}
                Err(e) => return Poll::Ready(Some(Err(e))),
            }

            // Need more data.
            match std::task::ready!(poll_read(&mut this.stream, cx, reader.buf_mut())) {
                Ok(0) => {
                    // EOF. Try decode with eof=true.
                    return Poll::Ready(reader.decode(&this.ctx, true, Instant::now()).transpose());
                }
                Ok(_) => {} // Loop to try decoding again.
                Err(e) => {
                    return Poll::Ready(Some(Err(reader.read_error(&this.ctx, e, Instant::now()))));
                }
            }
        }
    }
}

/// `Sink` impl for RTSP messages.
///
/// `poll_ready` is always ready: `start_send` appends to an unbounded write
/// buffer, after anything queued earlier, so internal callers may send a small
/// RTSP request without waiting for readiness. Bulk data is queued via
/// [`Connection::queue_write`] after [`Connection::poll_write_ready`] instead.
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
                    return std::task::Poll::Pending;
                }
            }
        }
        this.write_buf.clear();
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

    /// `written` counts bytes as they go out.
    #[tokio::test]
    async fn written() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let client = TcpStream::connect(listener.local_addr().unwrap())
            .await
            .unwrap();
        let mut conn = Connection::from_stream(client, usize::MAX).unwrap();
        assert_eq!(conn.written(), 0);
        conn.queue_write(b"$\x00\x00\x03abc");
        assert_eq!(conn.written(), 0);
        futures::SinkExt::<OwnedMessage>::flush(&mut conn)
            .await
            .unwrap();
        assert_eq!(conn.written(), 7);
        conn.queue_write(b"$\x01\x00\x02de");
        assert_eq!(conn.written(), 7);
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
                conn.queue_write(&[0; 1024]);
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

        let check = |r: Result<(), ErrorInt>| match r {
            Err(ErrorInt::WriteError { source, .. }) => {
                assert_eq!(source.kind(), kind);
                assert!(
                    source.to_string().contains("earlier write error"),
                    "{source}"
                );
            }
            o => panic!("expected write error, got {o:?}"),
        };
        conn.queue_write(b"x");
        assert!(conn.write_buf.is_empty());
        check(
            futures::SinkExt::<OwnedMessage>::send(
                &mut conn,
                OwnedMessage::Data {
                    channel_id: 0,
                    body: bytes::Bytes::from_static(b"x"),
                },
            )
            .await,
        );
        check(futures::SinkExt::<OwnedMessage>::flush(&mut conn).await);
        check(std::future::poll_fn(|cx| conn.poll_write_ready(cx)).await);
        assert!(conn.write_buf.is_empty());
        assert_eq!(conn.written(), written);
    }
}
