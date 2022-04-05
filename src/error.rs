// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{fmt::Display, sync::Arc};

use crate::{ConnectionContext, PacketContext, RtspMessageContext};
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
    #[error("[{conn_ctx}, {msg_ctx}] RTSP framing error: {description}")]
    RtspFramingError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        description: String,
    },

    #[error("[{conn_ctx}, {msg_ctx}] {status} response to {} CSeq={cseq}: \
             {description}", Into::<&str>::into(.method))]
    RtspResponseError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        method: rtsp_types::Method,
        cseq: u32,
        status: rtsp_types::StatusCode,
        description: String,
    },

    #[error(
        "[{conn_ctx}, {msg_ctx}] Received interleaved data on unassigned channel {channel_id}: \n\
         {:?}",
        crate::hex::LimitedHex::new(data, 64)
    )]
    RtspUnassignedChannelError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        channel_id: u8,
        data: Bytes,
    },

    #[error("[{conn_ctx}, {pkt_ctx} stream {stream_id}]: {description}")]
    PacketError {
        conn_ctx: ConnectionContext,
        pkt_ctx: PacketContext,
        stream_id: usize,
        description: String,
    },

    #[error(
        "[{conn_ctx}, {pkt_ctx}, stream={stream_id}, ssrc={ssrc:08x}, \
         seq={sequence_number:08x}] {description}"
    )]
    RtpPacketError {
        conn_ctx: ConnectionContext,
        pkt_ctx: crate::PacketContext,
        stream_id: usize,
        ssrc: u32,
        sequence_number: u16,
        description: String,
    },

    #[error("Unable to connect to RTSP server: {0}")]
    ConnectError(#[source] std::io::Error),

    #[error("[{conn_ctx}, {msg_ctx}] Error reading from RTSP peer: {source}")]
    RtspReadError {
        conn_ctx: ConnectionContext,
        msg_ctx: RtspMessageContext,
        source: std::io::Error,
    },

    #[error("[{conn_ctx}, {pkt_ctx}] Error receiving UDP packet: {source}")]
    UdpRecvError {
        conn_ctx: ConnectionContext,
        pkt_ctx: PacketContext,
        source: std::io::Error,
    },

    #[error("[{conn_ctx}] Error writing to RTSP peer: {source}")]
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
