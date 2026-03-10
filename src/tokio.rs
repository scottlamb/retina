// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use bytes::Bytes;
use futures::{Sink, Stream};
use std::time::Instant;
use tokio::io::AsyncWrite;
use tokio::net::{TcpStream, UdpSocket};
use url::Host;

use crate::buf::RingBuf;
use crate::inputs::Input;
use crate::rtsp::msg::OwnedMessage;
use crate::{Error, ErrorInt, RtspMessageContext};

use super::{ConnectionContext, ReceivedMessage, WallTime};

/// Default initial capacity for the read ring buffer (64 KiB).
const DEFAULT_READ_CAPACITY: usize = 64 * 1024;

/// A RTSP connection which implements `Stream`, `Sink`, and `Unpin`.
pub(crate) struct Connection {
    stream: TcpStream,
    ctx: ConnectionContext,
    parser: crate::rtsp::parse::Parser,
    read_buf: RingBuf,
    /// Write buffer for outgoing messages (written then flushed).
    write_buf: Vec<u8>,
}

impl Connection {
    pub(crate) async fn connect(host: Host<&str>, port: u16) -> Result<Self, std::io::Error> {
        let stream = match host {
            Host::Domain(h) => TcpStream::connect((h, port)).await,
            Host::Ipv4(h) => TcpStream::connect((h, port)).await,
            Host::Ipv6(h) => TcpStream::connect((h, port)).await,
        }?;
        Self::from_stream(stream)
    }

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
            parser: crate::rtsp::parse::Parser::default(),
            read_buf: RingBuf::new(DEFAULT_READ_CAPACITY),
            write_buf: Vec::new(),
        })
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.ctx
    }

    pub(crate) fn eof_ctx(&self) -> RtspMessageContext {
        RtspMessageContext {
            pos: self.parser.stream_pos() + self.read_buf.len() as u64,
            received_wall: WallTime::now(),
            received: Instant::now(),
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
    read_buf: &mut RingBuf,
    eof: bool,
) -> Result<Option<ReceivedMessage>, CodecError> {
    use crate::rtsp::parse::FeedError;

    let pos = parser.stream_pos();
    let mut input = read_buf.data_split();
    let initial_len = input.len();

    match parser.feed(&mut input) {
        Ok(None) => Ok(None), // idle, no data; caller distinguishes EOF from "need more"
        Ok(Some((msg, body_slice))) => {
            let consumed = initial_len - input.len();
            let body = Bytes::from(body_slice.to_owned());
            let start = read_buf.start();
            read_buf.advance_to(start + consumed as u64);
            Ok(Some(ReceivedMessage {
                msg,
                body,
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
                let start = read_buf.start();
                read_buf.advance_to(start + consumed as u64);
            }
            Ok(None)
        }
        Err(FeedError::Incomplete(_)) => {
            // EOF with incomplete data: the message is truncated.
            Err(CodecError::ParseError {
                description: format!(
                    "Incomplete RTSP message at EOF; buffered:\n{:#?}",
                    crate::hex::LimitedHex::from_split(read_buf.data_split(), 128),
                ),
                pos,
            })
        }
        Err(FeedError::Invalid(inv)) => Err(CodecError::ParseError {
            description: format!(
                "Invalid RTSP message: {inv}; buffered:\n{:#?}",
                crate::hex::LimitedHex::from_split(read_buf.data_split(), 128),
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
                    let pos = this.parser.stream_pos() + this.read_buf.len() as u64;
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
                    let pos = this.parser.stream_pos() + this.read_buf.len() as u64;
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
    read_buf: &RingBuf,
    e: CodecError,
) -> Error {
    wrap!(match e {
        CodecError::IoError(error) => ErrorInt::RtspReadError {
            conn_ctx: *ctx,
            msg_ctx: RtspMessageContext {
                pos: parser.stream_pos() + read_buf.len() as u64,
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

impl Sink<OwnedMessage> for Connection {
    type Error = ErrorInt;

    fn poll_ready(
        self: std::pin::Pin<&mut Self>,
        _cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        std::task::Poll::Ready(Ok(()))
    }

    fn start_send(
        mut self: std::pin::Pin<&mut Self>,
        item: OwnedMessage,
    ) -> Result<(), Self::Error> {
        self.write_buf.clear();
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

    #[test]
    fn crlf_data() {
        let mut read_buf = RingBuf::new(64);
        let data = b"\r\n$\x00\x00\x04asdfrest";
        let (first, _) = read_buf.spare_capacity(data.len());
        first[..data.len()].copy_from_slice(data);
        read_buf.advance_end(data.len());

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false)
            .unwrap()
            .unwrap();
        assert_eq!(&msg.body[..], b"asdf");
        assert_eq!(read_buf.len(), 4); // "rest" remains
    }

    #[test]
    fn response_decode() {
        let mut read_buf = RingBuf::new(64);
        let data = b"RTSP/1.0 200 OK\r\nCSeq: 1\r\n\r\n";
        let (first, _) = read_buf.spare_capacity(data.len());
        first[..data.len()].copy_from_slice(data);
        read_buf.advance_end(data.len());

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false)
            .unwrap()
            .unwrap();
        assert!(matches!(msg.msg, crate::rtsp::msg::Message::Response(_)));
        assert!(read_buf.is_empty());
    }
}
