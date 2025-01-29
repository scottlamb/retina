// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! tokio-based [`Connection`].
//!
//! In theory there could be a similar async-std-based implementation.

use bytes::{Buf, BufMut, Bytes, BytesMut};
use futures::{Sink, SinkExt, Stream, StreamExt};
use rtsp_types::{Data, Message};
use std::time::Instant;
use tokio::net::{TcpStream, UdpSocket};
use tokio_util::codec::Framed;
use url::Host;

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
                read_pos: 0,
            },
        )))
    }

    pub(crate) fn ctx(&self) -> &ConnectionContext {
        &self.0.codec().ctx
    }

    pub(crate) fn eof_ctx(&self) -> RtspMessageContext {
        RtspMessageContext {
            pos: self.0.codec().read_pos + crate::to_u64(self.0.read_buffer().remaining()),
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

impl Sink<Message<Bytes>> for Connection {
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
        item: Message<Bytes>,
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

    /// Number of bytes read and processed (drained from the input buffer).
    read_pos: u64,
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

impl Codec {
    fn parse_msg(&self, src: &mut BytesMut) -> Result<Option<(usize, Message<Bytes>)>, CodecError> {
        // Skip whitespace as `rtsp-types` does. It's important to also do it here, or we might
        // skip the our own data message encoding (next if) then hit
        // unreachable! after rtsp-types returns Message::Data.
        while src.starts_with(b"\r\n") {
            src.advance(2);
        }

        if !src.is_empty() && src[0] == b'$' {
            // Fast path for interleaved data, avoiding MessageRef -> Message<&[u8]> ->
            // Message<Bytes> conversion. This speeds things up quite a bit in practice,
            // avoiding a bunch of memmove calls.
            if src.len() < 4 {
                return Ok(None);
            }
            let channel_id = src[1];
            let len = 4 + usize::from(u16::from_be_bytes([src[2], src[3]]));
            if src.len() < len {
                src.reserve(len - src.len());
                return Ok(None);
            }
            let mut msg = src.split_to(len);
            msg.advance(4);
            return Ok(Some((
                len,
                Message::Data(Data::new(channel_id, msg.freeze())),
            )));
        }

        let (msg, len): (Message<&[u8]>, _) = match Message::parse(src) {
            Ok((m, l)) => (m, l),
            Err(rtsp_types::ParseError::Error) => {
                return Err(CodecError::ParseError {
                    description: format!(
                        "Invalid RTSP message; buffered:\n{:#?}",
                        crate::hex::LimitedHex::new(&src[..], 128),
                    ),
                    pos: self.read_pos,
                });
            }
            Err(rtsp_types::ParseError::Incomplete(_)) => return Ok(None),
        };

        // Map msg's body to a Bytes representation and advance `src`. Awkward:
        // 1.  lifetime concerns require mapping twice: first so the message
        //     doesn't depend on the BytesMut, which needs to be split/advanced;
        //     then to get the proper Bytes body in place post-split.
        // 2.  rtsp_types messages must be AsRef<[u8]>, so we can't use the
        //     range as an intermediate body.
        // 3.  within a match because the rtsp_types::Message enum itself
        //     doesn't have body/replace_body/map_body methods.
        let msg = match msg {
            Message::Request(msg) => {
                let body_range = crate::as_range(src, msg.body());
                let msg = msg.replace_body(rtsp_types::Empty);
                if let Some(r) = body_range {
                    let mut raw_msg = src.split_to(len);
                    raw_msg.advance(r.start);
                    raw_msg.truncate(r.len());
                    Message::Request(msg.replace_body(raw_msg.freeze()))
                } else {
                    src.advance(len);
                    Message::Request(msg.replace_body(Bytes::new()))
                }
            }
            Message::Response(msg) => {
                let body_range = crate::as_range(src, msg.body());
                let msg = msg.replace_body(rtsp_types::Empty);
                if let Some(r) = body_range {
                    let mut raw_msg = src.split_to(len);
                    raw_msg.advance(r.start);
                    raw_msg.truncate(r.len());
                    Message::Response(msg.replace_body(raw_msg.freeze()))
                } else {
                    src.advance(len);
                    Message::Response(msg.replace_body(Bytes::new()))
                }
            }
            Message::Data(_) => unreachable!(),
        };
        Ok(Some((len, msg)))
    }
}

impl tokio_util::codec::Decoder for Codec {
    type Item = ReceivedMessage;
    type Error = CodecError;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        let (len, msg) = match self.parse_msg(src) {
            Err(e) => return Err(e),
            Ok(None) => return Ok(None),
            Ok(Some((len, msg))) => (len, msg),
        };
        let msg = ReceivedMessage {
            msg,
            ctx: RtspMessageContext {
                pos: self.read_pos,
                received_wall: WallTime::now(),
                received: Instant::now(),
            },
        };
        self.read_pos += crate::to_u64(len);
        Ok(Some(msg))
    }
}

impl tokio_util::codec::Encoder<rtsp_types::Message<Bytes>> for Codec {
    type Error = CodecError;

    fn encode(
        &mut self,
        item: rtsp_types::Message<Bytes>,
        mut dst: &mut BytesMut,
    ) -> Result<(), Self::Error> {
        item.write(&mut (&mut dst).writer())
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
            read_pos: 0,
        };
        let mut buf = BytesMut::from(&b"\r\n$\x00\x00\x04asdfrest"[..]);
        codec.decode(&mut buf).unwrap();
        assert_eq!(&buf[..], b"rest");
    }
}
