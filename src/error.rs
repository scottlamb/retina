// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::sync::Arc;

use crate::{ConnectionContext, PacketContext, RtspMessageContext, StreamContext, WallTime};
use bytes::Bytes;

/// The error produced by `bail!` and `wrap!`, shared by the client and the
/// modules it uses.
///
/// This is private; each public API converts it to its module's error type
/// (such as `client::Error`) via `From`.
#[derive(Clone, derive_more::Debug, derive_more::Display)]
#[display("{_0}")]
#[debug("{_0:?}")]
pub(crate) struct Error(pub(crate) Arc<ErrorInt>);

#[derive(Debug, derive_more::Display, derive_more::Error)]
pub(crate) enum ErrorInt {
    /// The method's caller provided an invalid argument.
    #[display("Invalid argument: {_0}")]
    InvalidArgument(#[error(not(source))] String),

    /// Unparseable or unexpected RTSP message.
    #[display("RTSP framing error: {description}\n\nconn: {conn_ctx}\nmsg: {msg_ctx}")]
    RtspFramingError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        description: String,
    },

    #[display(
        "{status} response to {method} CSeq={cseq}: {description}\n\n\
             conn: {conn_ctx}\nmsg: {msg_ctx}"
    )]
    RtspResponseError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        method: crate::rtsp::msg::Method,
        cseq: u32,
        status: crate::rtsp::msg::StatusCode,
        description: String,
    },

    #[display(
        "Received interleaved data on unassigned channel {channel_id}: \n\
         {:?}\n\nconn: {conn_ctx}\nmsg: {msg_ctx}",
        crate::hex::LimitedHex::new(data, 64)
    )]
    RtspUnassignedChannelError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        channel_id: u8,
        data: Bytes,
    },

    #[display("{description}\n\nconn: {conn_ctx}\nstream: {stream_ctx}\npkt: {pkt_ctx}")]
    PacketError {
        conn_ctx: ConnectionContext,
        stream_ctx: StreamContext,
        pkt_ctx: PacketContext,
        stream_id: usize,
        description: String,
    },

    #[display(
        "{description}\n\n\
             conn: {conn_ctx}\nstream: {stream_ctx}\n\
             ssrc: {ssrc:08x}\nseq: {sequence_number}\npkt: {pkt_ctx}"
    )]
    RtpPacketError {
        conn_ctx: ConnectionContext,
        stream_ctx: StreamContext,
        pkt_ctx: crate::PacketContext,
        stream_id: usize,
        ssrc: u32,
        sequence_number: u16,
        description: String,
    },

    #[display("Unable to connect to RTSP server: {_0}")]
    ConnectError(#[error(source)] std::io::Error),

    #[display("Error reading from RTSP peer: {source}\n\nconn: {conn_ctx}\nmsg: {msg_ctx}")]
    RtspReadError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        #[error(source)]
        source: std::io::Error,
    },

    #[display(
        "Error receiving UDP packet: {source}\n\n\
             conn: {conn_ctx}\nstream: {stream_ctx}\nat: {when}"
    )]
    UdpRecvError {
        conn_ctx: ConnectionContext,
        stream_ctx: StreamContext,
        when: WallTime,
        #[error(source)]
        source: std::io::Error,
    },

    #[display("Error writing to RTSP peer: {source}\n\nconn: {conn_ctx}")]
    WriteError {
        conn_ctx: ConnectionContext,
        #[error(source)]
        source: std::io::Error,
    },

    #[display("Failed precondition: {_0}")]
    FailedPrecondition(#[error(not(source))] String),

    #[display("Internal error: {_0}")]
    Internal(#[error(source)] Box<dyn std::error::Error + Send + Sync>),

    #[display("Timeout")]
    Timeout,

    #[display("Unsupported: {_0}")]
    Unsupported(#[error(not(source))] String),
}
