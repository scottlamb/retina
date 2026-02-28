// Copyright (C) 2026 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Serving a stream over a WebSocket for use with the WebCodecs API.

use std::{io, net::SocketAddr, sync::Arc};

use anyhow::{Error, bail};
use axum::extract::{WebSocketUpgrade, ws::Message};
use bytes::{BufMut, Bytes, BytesMut};
use clap::Parser;
use futures::{StreamExt as _, stream::FuturesUnordered};
use log::{debug, info};
use retina::{
    client::SetupOptions,
    codec::{VideoFrame, VideoParameters},
};
use tokio::net::{TcpListener, TcpStream};
use tokio_rustls::TlsAcceptor;

#[derive(Parser)]
pub struct Opts {
    #[command(flatten)]
    src: super::Source,

    #[arg(long, default_value_t = (std::net::Ipv4Addr::UNSPECIFIED, 8080).into())]
    bind_addr: std::net::SocketAddr,

    /// Serve HTTPS with a self-signed certificate instead of plain HTTP.
    /// Browsers require a secure context for the WebCodecs API when not on localhost.
    #[arg(long)]
    tls: bool,
}

/// An axum `Listener` that wraps a `TcpListener` with TLS.
struct TlsListener {
    inner: TcpListener,
    acceptor: TlsAcceptor,
    #[allow(clippy::type_complexity)]
    handshaking: FuturesUnordered<
        std::pin::Pin<
            Box<
                dyn std::future::Future<
                        Output = (
                            io::Result<tokio_rustls::server::TlsStream<TcpStream>>,
                            SocketAddr,
                        ),
                    > + Send,
            >,
        >,
    >,
}

impl TlsListener {
    fn new(inner: TcpListener, acceptor: TlsAcceptor) -> Self {
        Self {
            inner,
            acceptor,
            handshaking: FuturesUnordered::new(),
        }
    }
}

impl axum::serve::Listener for TlsListener {
    type Io = tokio_rustls::server::TlsStream<TcpStream>;
    type Addr = SocketAddr;

    async fn accept(&mut self) -> (Self::Io, Self::Addr) {
        // Use FuturesUnordered so TLS handshakes run concurrently: accepting
        // connection N doesn't wait for connection N-1's handshake to finish.
        loop {
            tokio::select! {
                res = self.inner.accept() => {
                    match res {
                        Ok((stream, addr)) => {
                            let acceptor = self.acceptor.clone();
                            self.handshaking.push(Box::pin(async move {
                                (acceptor.accept(stream).await, addr)
                            }));
                        }
                        Err(e) => log::warn!("TCP accept error: {e}"),
                    }
                }
                Some((res, addr)) = self.handshaking.next(), if !self.handshaking.is_empty() => {
                    match res {
                        Ok(tls_stream) => return (tls_stream, addr),
                        Err(e) => log::warn!("TLS handshake error from {addr}: {e}"),
                    }
                }
            }
        }
    }

    fn local_addr(&self) -> io::Result<Self::Addr> {
        self.inner.local_addr()
    }
}

/// A frame ready to be broadcast to all websockets.
#[derive(Clone)]
struct FrameItem {
    parameters_id: u64,
    key_frame: bool,

    /// A message which should be sent iff the websocket has not yet seen `parameters_id`.
    parameters_update_msg: axum::extract::ws::Message,

    /// A message which should be sent unconditionally.
    frame_msg: axum::extract::ws::Message,
}

fn make_parameters_msg(parameters: &VideoParameters) -> axum::extract::ws::Message {
    let mut out = BytesMut::new();
    out.put_u8(0);
    out.put_slice(parameters.rfc6381_codec().as_bytes());
    out.put_u8(0);
    let (coded_width, coded_height) = parameters.coded_pixel_dimensions();
    out.put_u16(u16::try_from(coded_width).unwrap_or(u16::MAX));
    out.put_u16(u16::try_from(coded_height).unwrap_or(u16::MAX));
    out.put_slice(parameters.extra_data());
    axum::extract::ws::Message::Binary(out.freeze())
}

fn make_frame_msg(frame: &VideoFrame) -> axum::extract::ws::Message {
    let mut out = BytesMut::new();
    out.put_u8(1);
    out.put_i64(frame.timestamp().elapsed() * 1000 / 90); // XXX: shouldn't assume 90 kHz units.
    out.put_u8(frame.is_random_access_point().into());
    out.put_slice(frame.data());
    axum::extract::ws::Message::Binary(out.freeze())
}

/// Receives frames from the RTSP server and sends them to `frames_tx`.
async fn receive_frames(
    mut session: retina::client::Demuxed,
    frames_tx: tokio::sync::broadcast::Sender<FrameItem>,
) -> Result<(), Error> {
    let mut next_frame_num = 0;
    let mut cur_parameters = None;
    while let Some(item) = session.next().await {
        if let retina::codec::CodecItem::VideoFrame(frame) = item? {
            let stream_params = session.streams()[frame.stream_id()].parameters();
            let parameters = if let Some(cur_parameters) = cur_parameters.as_ref()
                && !frame.has_new_parameters()
            {
                cur_parameters
            } else if let Some((last_id, _)) = &cur_parameters {
                let Some(retina::codec::ParametersRef::Video(p)) = stream_params else {
                    unreachable!()
                };
                debug!("broadcasting parameter {}", last_id + 1);
                cur_parameters.insert((last_id + 1, make_parameters_msg(p)))
            } else if let Some(retina::codec::ParametersRef::Video(p)) = stream_params {
                debug!("broadcasting parameter 0");
                cur_parameters.insert((0, make_parameters_msg(p)))
            } else {
                continue; // wait for initial parameters.
            };
            debug!("broadcasting frame {next_frame_num}");
            next_frame_num += 1;
            let _ = frames_tx.send(FrameItem {
                parameters_id: parameters.0,
                key_frame: frame.is_random_access_point(),
                parameters_update_msg: parameters.1.clone(),
                frame_msg: make_frame_msg(&frame),
            });
        }
    }
    Ok(())
}

/// Serves a single websocket to a client.
async fn serve_websocket(
    mut socket: axum::extract::ws::WebSocket,
    mut frames_rx: tokio::sync::broadcast::Receiver<FrameItem>,
) {
    const KEEPALIVE_AFTER_IDLE: tokio::time::Duration = tokio::time::Duration::from_secs(30);
    let mut keepalive = tokio::time::interval(KEEPALIVE_AFTER_IDLE);
    keepalive.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
    let mut last_param_id: Option<u64> = None;
    let mut need_key_frame = true;
    let mut skipped = 0;
    loop {
        tokio::select! {
            res = frames_rx.recv() => {
                match res {
                    Ok(item) => {
                        if need_key_frame && !item.key_frame {
                            skipped += 1;
                            continue;
                        }
                        if skipped > 0 {
                            let mut out = BytesMut::new();
                            out.put_u8(2); // skipped frames msg.
                            out.put_u64(skipped);
                            if let Err(e) = socket.send(Message::Binary(out.freeze())).await {
                                log::error!("Failed to send skipped frames msg: {e}");
                                return;
                            }
                            skipped = 0;
                        }
                        if Some(item.parameters_id) != last_param_id {
                            if let Err(e) = socket.send(item.parameters_update_msg).await {
                                log::error!("Failed to send parameters update msg: {e}");
                                return;
                            }
                            last_param_id = Some(item.parameters_id);
                        }
                        if let Err(e) = socket.send(item.frame_msg).await {
                            log::error!("Failed to send frame msg: {e}");
                            return;
                        }
                        keepalive.reset_after(KEEPALIVE_AFTER_IDLE);
                        need_key_frame = false;
                    },
                    Err(tokio::sync::broadcast::error::RecvError::Lagged(frames)) => {
                        skipped += frames;
                        need_key_frame = true;
                        log::error!("Dropping {frames} frames");
                    }
                    Err(tokio::sync::broadcast::error::RecvError::Closed) => {
                        return;
                    }
                }
            }
            _ = keepalive.tick() => {
                if let Err(e) = socket.send(axum::extract::ws::Message::Ping(Bytes::new())).await {
                    log::error!("Failed to send keepalive: {e}");
                    return;
                }
            }
        }
    }
}

fn build_app(frames_tx: tokio::sync::broadcast::Sender<FrameItem>) -> axum::Router {
    let dir = std::path::Path::new("examples/client/src/webcodecs");
    let serve_dir = tower_http::services::ServeDir::new(dir);
    axum::Router::new()
        .route(
            "/websocket",
            axum::routing::any({
                let frames_tx = frames_tx.clone();
                async move |ws: WebSocketUpgrade| {
                    ws.on_upgrade(move |ws| serve_websocket(ws, frames_tx.subscribe()))
                }
            }),
        )
        .fallback_service(serve_dir)
        .layer(tower_http::trace::TraceLayer::new_for_http())
}

fn build_tls_acceptor() -> Result<TlsAcceptor, Error> {
    let cert = rcgen::generate_simple_self_signed(vec!["localhost".to_owned()])?;
    let key = rustls::pki_types::PrivateKeyDer::try_from(cert.signing_key.serialize_der()).unwrap();
    let cert_der = rustls::pki_types::CertificateDer::from(cert.cert);
    let config = rustls::ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(vec![cert_der], key)?;
    Ok(TlsAcceptor::from(Arc::new(config)))
}

async fn serve_clients(
    listener: TcpListener,
    tls: bool,
    frames_tx: tokio::sync::broadcast::Sender<FrameItem>,
) -> Result<(), Error> {
    let dir = std::path::Path::new("examples/client/src/webcodecs");
    if !tokio::fs::try_exists(dir).await.is_ok_and(|res| res) {
        bail!(
            "Unable to access directory {}; can't serve static file tree",
            dir.display()
        );
    }
    let app = build_app(frames_tx);
    if tls {
        let acceptor = build_tls_acceptor()?;
        let tls_listener = TlsListener::new(listener, acceptor);
        axum::serve(tls_listener, app).await?;
    } else {
        axum::serve(listener, app).await?;
    }
    Ok(())
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    let creds = super::creds(opts.src.username.clone(), opts.src.password.clone());
    let mut session = retina::client::Session::describe(
        opts.src.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina webcodecs example".to_owned()),
    )
    .await?;

    let video_stream_i = session.streams().iter().position(|s| {
        if s.media() == "video" {
            let encoding_name = s.encoding_name();
            if matches!(encoding_name, "h264" | "h265" | "jpeg") {
                log::info!("Using {encoding_name} video stream");
                return true;
            }
            log::info!(
                "Ignoring {} video stream because it's unsupported",
                s.encoding_name(),
            );
        }
        false
    });
    let Some(video_stream_i) = video_stream_i else {
        bail!("No suitable video stream found");
    };
    session
        .setup(video_stream_i, SetupOptions::default())
        .await?;
    let session = session
        .play(retina::client::PlayOptions::default())
        .await?
        .demuxed()?;

    let listener = TcpListener::bind(&opts.bind_addr).await?;
    let scheme = if opts.tls { "https" } else { "http" };
    info!("Listening on {scheme}://{}", listener.local_addr()?);
    let (frames_tx, _) = tokio::sync::broadcast::channel(64);
    let frames_tx2 = frames_tx.clone();
    let stop_signal = tokio::signal::ctrl_c();

    tokio::select! {
        res = receive_frames(session, frames_tx) => {
            info!("RTSP session ending: {res:?}");
        }
        res = serve_clients(listener, opts.tls, frames_tx2) => {
            info!("Axum shutting down: {res:?}");
        }
        _ = stop_signal => {
            info!("Received stop signal");
        }
    }
    Ok(())
}
