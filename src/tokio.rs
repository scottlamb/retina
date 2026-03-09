// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use bytes::{Buf, BufMut, Bytes, BytesMut};
use futures::{Sink, SinkExt, Stream, StreamExt};
use std::time::Instant;
use tokio::net::{TcpStream, UdpSocket};
use tokio_util::codec::Framed;
use url::Host;

use crate::rtsp::msg::OwnedMessage;
use crate::{Error, ErrorInt, RtspMessageContext};

use super::{ConnectionContext, ReceivedMessage, WallTime};

/// A RTSP connection which implements `Stream`, `Sink`, and `Unpin`.
pub(crate) struct Connection(Framed<TcpStream, Codec>);

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
        Ok(Self(Framed::new(
            stream,
            Codec {
                ctx: ConnectionContext {
                    local_addr,
                    peer_addr,
                    established_wall,
                },
                parser: crate::rtsp::parse::Parser::default(),
            },
        )))
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.0.codec().ctx
    }

    pub(crate) fn eof_ctx(&self) -> RtspMessageContext {
        RtspMessageContext {
            pos: self.0.codec().parser.stream_pos()
                + crate::to_u64(self.0.read_buffer().remaining()),
            received_wall: WallTime::now(),
            received: Instant::now(),
        }
    }

    fn wrap_write_err(&self, e: CodecError) -> ErrorInt {
        match e {
            CodecError::IoError(source) => ErrorInt::WriteError {
                conn_ctx: *self.ctx(),
                source,
            },
            CodecError::ParseError { .. } => unreachable!(),
        }
    }
}

impl Stream for Connection {
    type Item = Result<ReceivedMessage, Error>;

    fn poll_next(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Option<Self::Item>> {
        self.0.poll_next_unpin(cx).map_err(|e| {
            wrap!(match e {
                CodecError::IoError(error) => ErrorInt::RtspReadError {
                    conn_ctx: *self.ctx(),
                    msg_ctx: self.eof_ctx(),
                    source: error,
                },
                CodecError::ParseError { description, pos } => ErrorInt::RtspFramingError {
                    conn_ctx: *self.ctx(),
                    msg_ctx: RtspMessageContext {
                        pos,
                        received_wall: WallTime::now(),
                        received: Instant::now(),
                    },
                    description,
                },
            })
        })
    }
}

impl Sink<OwnedMessage> for Connection {
    type Error = ErrorInt;

    fn poll_ready(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        self.0
            .poll_ready_unpin(cx)
            .map_err(|e| self.wrap_write_err(e))
    }

    fn start_send(
        mut self: std::pin::Pin<&mut Self>,
        item: OwnedMessage,
    ) -> Result<(), Self::Error> {
        self.0
            .start_send_unpin(item)
            .map_err(|e| self.wrap_write_err(e))
    }

    fn poll_flush(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        self.0
            .poll_flush_unpin(cx)
            .map_err(|e| self.wrap_write_err(e))
    }

    fn poll_close(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Result<(), Self::Error>> {
        self.0
            .poll_close_unpin(cx)
            .map_err(|e| self.wrap_write_err(e))
    }
}

/// Encodes and decodes RTSP messages.
struct Codec {
    ctx: ConnectionContext,
    parser: crate::rtsp::parse::Parser,
}

/// An intermediate error type that exists because [`Framed`] expects the
/// codec's error type to implement `From<std::io::Error>`, and [`Error`]
/// takes additional context.
#[derive(Debug)]
enum CodecError {
    IoError(std::io::Error),
    ParseError { description: String, pos: u64 },
}

impl std::convert::From<std::io::Error> for CodecError {
    fn from(e: std::io::Error) -> Self {
        CodecError::IoError(e)
    }
}

impl tokio_util::codec::Decoder for Codec {
    type Item = ReceivedMessage;
    type Error = CodecError;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        use crate::rtsp::inputs::{Contiguous, Input as _};
        use crate::rtsp::parse::FeedError;

        let pos = self.parser.stream_pos();
        let initial_len = src.len();

        // Feed the parser. We extract (msg, body_len, consumed) or error
        // info before dropping the Contiguous borrow on `src`.
        enum FeedResult {
            None,
            Message {
                msg: crate::rtsp::msg::Message,
                body_len: usize,
                consumed: usize,
            },
            Incomplete {
                needed: Option<std::num::NonZeroUsize>,
                consumed: usize,
            },
            Invalid(crate::rtsp::parse::Invalid),
        }

        let feed_result = {
            let mut input = Contiguous::new(src, true);
            let r = self.parser.feed(&mut input);
            let consumed = initial_len - input.len();
            match r {
                Ok(None) => FeedResult::None,
                Ok(Some((msg, body_slice))) => FeedResult::Message {
                    msg,
                    body_len: body_slice.len(),
                    consumed,
                },
                Err(FeedError::Incomplete(needed)) => FeedResult::Incomplete { needed, consumed },
                Err(FeedError::Invalid(inv)) => FeedResult::Invalid(inv),
            }
        };

        match feed_result {
            FeedResult::None => Ok(None),
            FeedResult::Message {
                msg,
                body_len,
                consumed,
            } => {
                let body = if body_len == 0 {
                    let _ = src.split_to(consumed);
                    Bytes::new()
                } else {
                    let mut raw = src.split_to(consumed);
                    let before_body = consumed - body_len;
                    raw.advance(before_body);
                    raw.truncate(body_len);
                    raw.freeze()
                };
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
            FeedResult::Incomplete { needed, consumed } => {
                // Advance past any bytes the parser stably consumed (e.g. headers).
                if consumed > 0 {
                    src.advance(consumed);
                }
                // Reserve space for the body if the parser knows how much is needed.
                src.reserve(needed.map(|n| n.get()).unwrap_or(1024));
                Ok(None)
            }
            FeedResult::Invalid(inv) => Err(CodecError::ParseError {
                description: format!(
                    "Invalid RTSP message: {inv}; buffered:\n{:#?}",
                    crate::hex::LimitedHex::new(&src[..], 128),
                ),
                pos: inv.pos,
            }),
        }
    }
}

impl tokio_util::codec::Encoder<OwnedMessage> for Codec {
    type Error = CodecError;

    fn encode(&mut self, item: OwnedMessage, dst: &mut BytesMut) -> Result<(), Self::Error> {
        item.write(&mut dst.writer())
            .expect("BufMut Writer is infallible");
        Ok(())
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
    use tokio_util::codec::Decoder;

    use super::*;

    #[test]
    fn crlf_data() {
        let mut codec = Codec {
            ctx: ConnectionContext::dummy(),
            parser: crate::rtsp::parse::Parser::default(),
        };
        let mut buf = BytesMut::from(&b"\r\n$\x00\x00\x04asdfrest"[..]);
        codec.decode(&mut buf).unwrap();
        assert_eq!(&buf[..], b"rest");
    }
}
