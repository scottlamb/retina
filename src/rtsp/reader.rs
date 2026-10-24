// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sans-I/O reading of RTSP messages from a ring buffer; see [`Reader`].

use std::time::Instant;

use crate::buf::MarkBuf;
use crate::inputs::Split;
use crate::{ConnectionContext, Error, ErrorInt, ReceivedMessage, RtspMessageContext, WallTime};

/// Default initial capacity for the read ring buffer (64 KiB).
const DEFAULT_READ_CAPACITY: usize = 64 * 1024;

/// An RTSP message parser and the ring buffer it reads from.
///
/// The caller fills [`Reader::buf_mut`] with bytes received on the connection
/// and calls [`Reader::decode`] to parse messages out of them.
pub(crate) struct Reader {
    parser: crate::rtsp::parse::Parser,
    buf: MarkBuf,
}

impl Default for Reader {
    fn default() -> Self {
        Self {
            parser: crate::rtsp::parse::Parser::default(),
            buf: MarkBuf::new(DEFAULT_READ_CAPACITY),
        }
    }
}

impl Reader {
    /// Returns a reader which rejects messages larger than `max_message_size`
    /// (see [`crate::rtsp::parse::ParserBuilder::max_message_size`]) and
    /// whose buffer retains at most `max_retained` bytes for marks (see
    /// [`MarkBuf::set_max_retained`]).
    pub(crate) fn new(max_message_size: usize, max_retained: usize) -> Self {
        let mut buf = MarkBuf::new(DEFAULT_READ_CAPACITY);
        buf.set_max_retained(max_retained);
        Self {
            parser: crate::rtsp::parse::Parser::builder()
                .max_message_size(max_message_size)
                .build(),
            buf,
        }
    }

    #[inline]
    pub(crate) fn buf(&self) -> &MarkBuf {
        &self.buf
    }

    #[inline]
    pub(crate) fn buf_mut(&mut self) -> &mut MarkBuf {
        &mut self.buf
    }

    /// Parses the next message from buffered data, if a complete one is
    /// available.
    ///
    /// `eof` should be true iff the connection has been closed, so that a
    /// partial message is an error rather than a reason to wait for more data.
    pub(crate) fn decode(
        &mut self,
        conn_ctx: &ConnectionContext,
        eof: bool,
        now: Instant,
    ) -> Result<Option<ReceivedMessage>, Error> {
        try_decode(&mut self.parser, &mut self.buf, eof, now).map_err(|e| {
            wrap!(ErrorInt::RtspFramingError {
                conn_ctx: *conn_ctx,
                msg_ctx: RtspMessageContext {
                    pos: e.pos,
                    received_wall: WallTime::now(),
                    received: now,
                },
                description: e.description,
            })
        })
    }

    /// Returns a context for the position just past all buffered data, e.g.
    /// for errors at end of stream.
    pub(crate) fn eof_ctx(&self, now: Instant) -> RtspMessageContext {
        RtspMessageContext {
            pos: self.parser.stream_pos() + self.buf.unparsed_len() as u64,
            received_wall: WallTime::now(),
            received: now,
        }
    }

    /// Returns an error for a failed read from the connection.
    pub(crate) fn read_error(
        &self,
        conn_ctx: &ConnectionContext,
        source: std::io::Error,
        now: Instant,
    ) -> Error {
        wrap!(ErrorInt::RtspReadError {
            conn_ctx: *conn_ctx,
            msg_ctx: self.eof_ctx(now),
            source,
        })
    }

    /// Returns a message body (or other range of buffered data) as `Bytes`.
    ///
    /// This copies the data out, so it's for cold paths: RTSP message bodies
    /// and RTCP packets. RTP packets are lent out directly from the ring
    /// buffer; see [`crate::client::RtpPacket`].
    pub(crate) fn body_bytes(&self, body_pos: u64, body_len: u32) -> bytes::Bytes {
        bytes::Bytes::from(self.buf.split(body_pos, body_len as usize).to_vec())
    }
}

/// A framing error from [`try_decode`].
#[derive(Debug)]
struct DecodeError {
    description: String,
    pos: u64,
}

/// Tries to decode a message from the read buffer without I/O.
///
/// When `eof` is true, the TCP stream has closed. `Incomplete` is promoted to
/// an error. `Ok(None)` means idle between messages, possibly after consuming
/// blank lines, whether or not `eof` is true.
fn try_decode(
    parser: &mut crate::rtsp::parse::Parser,
    read_buf: &mut MarkBuf,
    eof: bool,
    now: Instant,
) -> Result<Option<ReceivedMessage>, DecodeError> {
    use crate::rtsp::parse::FeedError;

    let unparsed = read_buf.unparsed();
    let mut input = {
        let split = read_buf.unparsed_split();
        let (first, second) = split.slices();
        Split::new(first, second)
    };
    let initial_len = input.len();

    match parser.feed(&mut input) {
        Ok(None) => {
            // Idle between messages. Blank lines before here may have been consumed: advance past
            // them so they are not parsed again. The caller tells a clean EOF from "need more".
            let consumed = initial_len - input.len();
            if consumed > 0 {
                read_buf.advance_unparsed(unparsed + consumed as u64);
            }
            Ok(None)
        }
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
                    // Where the message began, which can be in an earlier read than this one when
                    // its head arrived in pieces; the parser's position at this call's start is not.
                    pos: parser.msg_start_pos(),
                    received_wall: WallTime::now(),
                    received: now,
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
            Err(DecodeError {
                description: format!(
                    "Incomplete RTSP message at EOF ({inc}); buffered:\n{:#?}",
                    crate::hex::LimitedHex::from_split(read_buf.unparsed_split(), 128),
                ),
                // The truncated message's own start (it may have begun in an earlier read).
                pos: parser.msg_start_pos(),
            })
        }
        Err(FeedError::Invalid(inv)) => Err(DecodeError {
            description: format!(
                "Invalid RTSP message: {inv}; buffered:\n{:#?}",
                crate::hex::LimitedHex::from_split(read_buf.unparsed_split(), 128),
            ),
            pos: inv.pos,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A message's `pos` is where it began in the stream, even when its head arrives in pieces
    /// and the parser stably consumed part of it on an earlier read, and after the blank line some
    /// servers send between messages.
    #[test]
    fn message_pos_is_the_message_start_across_reads() {
        let mut read_buf = MarkBuf::new(256);
        let mut parser = crate::rtsp::parse::Parser::default();

        // An interleaved frame at stream position 0.
        read_buf.extend(b"$\x00\x00\x04asdf");
        let data = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert_eq!(data.ctx.pos, 0);

        // A blank line, then a response whose head arrives over three reads. It starts at
        // 8 + 2 = 10. The first read ends mid-header, so the parser stably consumes the
        // status line before returning `Incomplete`.
        read_buf.extend(b"\r\nRTSP/1.0 200 OK\r\nCSe");
        assert!(
            try_decode(&mut parser, &mut read_buf, false, Instant::now())
                .unwrap()
                .is_none()
        );
        read_buf.extend(b"q: 1\r\n");
        assert!(
            try_decode(&mut parser, &mut read_buf, false, Instant::now())
                .unwrap()
                .is_none()
        );
        read_buf.extend(b"\r\n$\x00\x00\x02hi");
        let resp = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert!(matches!(resp.msg, crate::rtsp::msg::Message::Response(_)));
        assert_eq!(resp.ctx.pos, 10);

        // The next frame starts right after the response's head (10 + 17 + 9 + 2 = 38).
        let data = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert_eq!(data.ctx.pos, 38);
    }

    /// Blank lines right before the end of the stream close it cleanly: they are not a truncated
    /// message.
    #[test]
    fn blank_lines_before_eof_close_cleanly() {
        let mut read_buf = MarkBuf::new(256);
        let mut parser = crate::rtsp::parse::Parser::default();
        read_buf.extend(b"$\x00\x00\x02hi\r\n\r\n");
        let data = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert_eq!(data.ctx.pos, 0);
        // The blank lines are consumed, once.
        assert!(
            try_decode(&mut parser, &mut read_buf, false, Instant::now())
                .unwrap()
                .is_none()
        );
        assert_eq!(read_buf.unparsed_len(), 0);
        assert_eq!(parser.stream_pos(), 6 + 4);
        // EOF now is a clean close, not an error.
        assert!(
            try_decode(&mut parser, &mut read_buf, true, Instant::now())
                .unwrap()
                .is_none()
        );

        // The same when the blank lines and EOF arrive together.
        let mut read_buf = MarkBuf::new(256);
        let mut parser = crate::rtsp::parse::Parser::default();
        read_buf.extend(b"\r\n\r\n");
        assert!(
            try_decode(&mut parser, &mut read_buf, true, Instant::now())
                .unwrap()
                .is_none()
        );
        assert_eq!(read_buf.unparsed_len(), 0);
        assert_eq!(parser.stream_pos(), 4);
    }

    /// A message truncated by EOF reports its own start, not where the final read began.
    #[test]
    fn truncated_message_pos_is_its_start() {
        let mut read_buf = MarkBuf::new(256);
        let mut parser = crate::rtsp::parse::Parser::default();
        read_buf.extend(b"$\x00\x00\x01xRTSP/1.0 200 OK\r\nCSeq: 1\r\n");
        let data = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert_eq!(data.ctx.pos, 0);
        assert!(
            try_decode(&mut parser, &mut read_buf, false, Instant::now())
                .unwrap()
                .is_none()
        );
        match try_decode(&mut parser, &mut read_buf, true, Instant::now()) {
            Err(DecodeError { pos, .. }) => assert_eq!(pos, 5),
            other => panic!("expected a truncation error, got {other:?}"),
        }
    }

    #[test]
    fn crlf_data() {
        let mut read_buf = MarkBuf::new(64);
        read_buf.extend(b"\r\n$\x00\x00\x04asdfrest");

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        // Read body from ring buffer.
        let (s1, s2) = read_buf.split(msg.body_pos, msg.body_len as usize).slices();
        assert_eq!(s1, b"asdf");
        assert!(s2.is_empty());
        assert_eq!(read_buf.unparsed_len(), 4); // "rest" remains
    }

    #[test]
    fn response_decode() {
        let mut read_buf = MarkBuf::new(64);
        read_buf.extend(b"RTSP/1.0 200 OK\r\nCSeq: 1\r\n\r\n");

        let mut parser = crate::rtsp::parse::Parser::default();
        let msg = try_decode(&mut parser, &mut read_buf, false, Instant::now())
            .unwrap()
            .unwrap();
        assert!(matches!(msg.msg, crate::rtsp::msg::Message::Response(_)));
        assert_eq!(msg.body_len, 0);
        assert_eq!(read_buf.unparsed_len(), 0);
    }
}
