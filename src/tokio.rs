// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use futures::Sink;
use std::task::{Context, Poll};
use tokio::io::AsyncWrite;
use tokio::net::{TcpStream, UdpSocket};
use url::Host;

use crate::buf::MarkBuf;
use crate::rtsp::msg::OwnedMessage;
use crate::rtsp::reader::Reader;
use crate::{ConnectionContext, ErrorInt, WallTime};
#[cfg(test)]
use crate::{Error, ReceivedMessage};
#[cfg(test)]
use futures::Stream;
#[cfg(test)]
use std::time::Instant;

/// A RTSP connection which implements `Sink`, `Unpin`, and (in tests, for
/// mock servers) `Stream`.
///
/// The client reads into a sans-I/O core's buffer via
/// [`Connection::poll_read`] instead of using the `Stream` impl.
pub(crate) struct Connection {
    stream: TcpStream,
    ctx: ConnectionContext,

    /// The reader for the `Stream` impl; see [`Connection::with_reader`].
    #[cfg_attr(not(test), allow(dead_code))]
    reader: Option<Reader>,

    /// Write buffer for outgoing messages (appended then flushed).
    write_buf: Vec<u8>,
}

impl Connection {
    /// Connects to `host:port`, from `bind_addr` if specified.
    ///
    /// The connection has no reader; the caller parses what it reads via a
    /// sans-I/O core.
    pub(crate) async fn connect(
        host: Host<&str>,
        port: u16,
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
        Self::from_stream(stream)
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

    /// Wraps `stream`, without a reader; see [`Connection::with_reader`].
    pub(crate) fn from_stream(stream: TcpStream) -> Result<Self, std::io::Error> {
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
            reader: None,
            write_buf: Vec::new(),
        })
    }

    /// Adds a reader, so this connection can be used via its `Stream` impl.
    #[cfg(test)]
    pub(crate) fn with_reader(mut self, max_message_size: usize) -> Self {
        self.reader = Some(Reader::new(max_message_size, usize::MAX));
        self
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.ctx
    }

    /// Reads body data from the ring buffer as `Bytes`; see [`Reader::body_bytes`].
    #[cfg(test)]
    pub(crate) fn body_bytes(&self, body_pos: u64, body_len: u32) -> bytes::Bytes {
        self.reader
            .as_ref()
            .expect("with_reader")
            .body_bytes(body_pos, body_len)
    }

    /// Reads available bytes from the connection into `buf`, returning the
    /// number read. `Ready(Ok(0))` means the peer closed the connection.
    pub(crate) fn poll_read(
        &self,
        cx: &mut Context<'_>,
        buf: &mut MarkBuf,
    ) -> Poll<std::io::Result<usize>> {
        poll_read(&self.stream, cx, buf)
    }

    /// Writes from `bufs` (a sans-I/O core's transmit buffer), returning the
    /// number of bytes written.
    ///
    /// The client writes only this way, bypassing the `Sink` impl.
    pub(crate) fn poll_write_vectored(
        &mut self,
        cx: &mut Context<'_>,
        bufs: (&[u8], &[u8]),
    ) -> Poll<Result<usize, ErrorInt>> {
        debug_assert!(self.write_buf.is_empty());
        let bufs = [std::io::IoSlice::new(bufs.0), std::io::IoSlice::new(bufs.1)];
        let r = match std::pin::Pin::new(&mut self.stream).poll_write_vectored(cx, &bufs) {
            Poll::Ready(Ok(0)) => Err(std::io::ErrorKind::WriteZero.into()),
            Poll::Ready(r) => r,
            Poll::Pending => return Poll::Pending,
        };
        Poll::Ready(r.map_err(|source| ErrorInt::WriteError {
            conn_ctx: self.ctx,
            source,
        }))
    }
}

/// Reads available bytes from `stream` into `buf`'s spare capacity via
/// vectored I/O, filling both halves of the ring.
fn poll_read(
    stream: &TcpStream,
    cx: &mut Context<'_>,
    buf: &mut MarkBuf,
) -> Poll<std::io::Result<usize>> {
    loop {
        std::task::ready!(stream.poll_read_ready(cx))?;
        let (first, second) = buf.spare_capacity(4096);
        let mut bufs = [
            std::io::IoSliceMut::new(first),
            std::io::IoSliceMut::new(second),
        ];
        match stream.try_read_vectored(&mut bufs) {
            Ok(n) => {
                buf.advance_end(n);
                return Poll::Ready(Ok(n));
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                // Spurious readiness; re-register and wait.
                continue;
            }
            Err(e) => return Poll::Ready(Err(e)),
        }
    }
}

#[cfg(test)]
impl Stream for Connection {
    type Item = Result<ReceivedMessage, Error>;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        let this = &mut *self;
        let reader = this.reader.as_mut().expect("with_reader");
        loop {
            // Try decoding from existing buffered data.
            match reader.decode(&this.ctx, false, Instant::now()) {
                Ok(Some(msg)) => return Poll::Ready(Some(Ok(msg))),
                Ok(None) => {}
                Err(e) => return Poll::Ready(Some(Err(e))),
            }

            // Need more data.
            match std::task::ready!(poll_read(&this.stream, cx, reader.buf_mut())) {
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
        item.write(&mut self.write_buf)
            .expect("Vec Writer is infallible");
        Ok(())
    }

    fn poll_flush(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        let this = &mut *self;
        while !this.write_buf.is_empty() {
            match std::pin::Pin::new(&mut this.stream).poll_write(cx, &this.write_buf) {
                std::task::Poll::Ready(Ok(n)) => {
                    this.write_buf.drain(..n);
                }
                std::task::Poll::Ready(Err(e)) => {
                    return std::task::Poll::Ready(Err(ErrorInt::WriteError {
                        conn_ctx: this.ctx,
                        source: e,
                    }));
                }
                std::task::Poll::Pending => return std::task::Poll::Pending,
            }
        }
        match std::pin::Pin::new(&mut this.stream).poll_flush(cx) {
            std::task::Poll::Ready(Ok(())) => std::task::Poll::Ready(Ok(())),
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(ErrorInt::WriteError {
                conn_ctx: this.ctx,
                source: e,
            })),
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
            std::task::Poll::Ready(Err(e)) => std::task::Poll::Ready(Err(ErrorInt::WriteError {
                conn_ctx: this.ctx,
                source: e,
            })),
            std::task::Poll::Pending => std::task::Poll::Pending,
        }
    }
}

/// tokio-specific version of [`crate::udp_pair::UdpPair`].
pub(crate) struct UdpPair {
    pub(crate) rtp_port: u16,
    pub(crate) rtp_socket: UdpSocket,
    pub(crate) rtcp_socket: UdpSocket,
}

impl UdpPair {
    pub(crate) fn for_ip(ip_addr: std::net::IpAddr) -> Result<Self, std::io::Error> {
        let inner = crate::udp_pair::UdpPair::for_ip(ip_addr)?;
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
            Connection::connect(Host::Ipv4(std::net::Ipv4Addr::LOCALHOST), port, Some(local)),
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
        let mut client = Connection::from_stream(client.unwrap()).unwrap();
        let mut server = Connection::from_stream(server.unwrap().0)
            .unwrap()
            .with_reader(usize::MAX);

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
}
