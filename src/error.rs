// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{fmt::Display, sync::Arc};

use crate::{ConnectionContext, PacketContext, RtspMessageContext, StreamContext, WallTime};
use bytes::Bytes;
use thiserror::Error;

/// An opaque `std::error::Error + Send + Sync + 'static` implementation.
///
/// Currently the focus is on providing detailed human-readable error messages.
/// In most cases they have enough information to find the offending packet
/// in Wireshark.
///
/// If you wish to inspect Retina errors programmatically, or if you need
/// errors formatted in a different way, please file an issue on the `retina`
/// repository.
#[derive(Clone)]
pub struct Error(pub(crate) Arc<ErrorInt>);

impl Error {
    /// Returns the status code, if the error was generated from a response.
    pub fn status_code(&self) -> Option<u16> {
        match self.0.as_ref() {
            ErrorInt::RtspResponseError { status, .. } => Some((*status).into()),
            _ => None,
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.0, f)
    }
}

impl std::error::Error for Error {}

#[derive(Debug, Error)]
pub(crate) enum ErrorInt {
    /// The method's caller provided an invalid argument.
    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    /// Unparseable or unexpected RTSP message.
    #[error("RTSP framing error: {description}\n\nconn: {conn_ctx}\nmsg: {msg_ctx}")]
    RtspFramingError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        description: String,
    },

    #[error("{status} response to {} CSeq={cseq}: {description}\n\n\
             conn: {conn_ctx}\nmsg: {msg_ctx}", Into::<&str>::into(.method))]
    RtspResponseError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        method: rtsp_types::Method,
        cseq: u32,
        status: rtsp_types::StatusCode,
        description: String,
    },

    #[error(
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

    #[error("{description}\n\nconn: {conn_ctx}\nstream: {stream_ctx}\npkt: {pkt_ctx}")]
    PacketError {
        conn_ctx: ConnectionContext,
        stream_ctx: StreamContext,
        pkt_ctx: PacketContext,
        stream_id: usize,
        description: String,
    },

    #[error(
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

    #[error("Unable to connect to RTSP server: {0}")]
    ConnectError(#[source] std::io::Error),

    #[error("Error reading from RTSP peer: {source}\n\nconn: {conn_ctx}\nmsg: {msg_ctx}")]
    RtspReadError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        source: std::io::Error,
    },

    #[error(
        "Error receiving UDP packet: {source}\n\n\
             conn: {conn_ctx}\nstream: {stream_ctx}\nat: {when}"
    )]
    UdpRecvError {
        conn_ctx: ConnectionContext,
        stream_ctx: StreamContext,
        when: WallTime,
        source: std::io::Error,
    },

    #[error("Error writing to RTSP peer: {source}\n\nconn: {conn_ctx}")]
    WriteError {
        conn_ctx: ConnectionContext,
        source: std::io::Error,
    },

    #[error("Failed precondition: {0}")]
    FailedPrecondition(String),

    #[error("Internal error: {0}")]
    Internal(#[source] Box<dyn std::error::Error + Send + Sync>),

    #[error("Timeout")]
    Timeout,
}
