// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A downstream RTSP connection: a tokio driver around
//! [`retina::server::ConnectionCore`].

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use anyhow::Error;
use log::{debug, info};
use retina::rtp::Sender;
use retina::rtsp::msg::StatusCode;
use retina::server::{ConnectionCore, Event, RtpInfo, SdpMedia, ServerOptions};
use tokio::time::Instant;

use crate::fanout::{ConnOut, Downstream};
use crate::{Proxy, TrackKind};

/// How long `DESCRIBE` waits for the upstream to supply codec parameters.
const DESCRIBE_TIMEOUT: Duration = Duration::from_secs(10);

/// The proxy's data for each stream set up within a session.
struct SetupStream {
    track_i: usize,
    sender: Option<Sender>,
    alive: Arc<AtomicBool>,
}

pub async fn serve(proxy: Arc<Proxy>, stream: tokio::net::TcpStream) -> Result<(), Error> {
    stream.set_nodelay(true)?;
    let mut core = ConnectionCore::<SetupStream>::new(
        stream.local_addr()?,
        stream.peer_addr()?,
        ServerOptions::default().server("Retina proxy example"),
    );
    let (r, w) = stream.into_split();
    let out = Arc::new(ConnOut::new());
    let writer = tokio::spawn({
        let out = out.clone();
        async move { out.write_loop(w).await }
    });
    let result = read_loop(&proxy, &mut core, &out, &r).await;

    // Stop the upstream task from sending to this connection.
    for (_, streams) in core.sessions() {
        for s in streams {
            s.data.alive.store(false, Ordering::Relaxed);
        }
    }
    out.close();
    match writer.await {
        Ok(Err(e)) if result.is_ok() => Err(e.into()),
        _ => result,
    }
}

async fn read_loop(
    proxy: &Proxy,
    core: &mut ConnectionCore<SetupStream>,
    out: &Arc<ConnOut>,
    r: &tokio::net::tcp::OwnedReadHalf,
) -> Result<(), Error> {
    let mut eof = false;
    loop {
        loop {
            let Some(event) = core.poll_event(Instant::now().into_std()) else {
                break;
            };
            let joins = handle_event(proxy, out, event?).await;

            // Write any response before the new downstreams' first packets.
            if let Some(t) = core.poll_transmit() {
                out.write_rtsp(&t);
            }
            for (track_i, d) in joins {
                // The upstream task only goes away on error, which ends the process.
                let _ = proxy.tracks[track_i].joins.send(d);
            }
        }
        if let Some(t) = core.poll_transmit() {
            out.write_rtsp(&t);
        }
        if eof || out.is_closed() {
            return Ok(());
        }
        let deadline = core.poll_timeout();
        tokio::select! {
            readable = r.readable() => {
                readable?;
                let (spare, _) = core.read_buf().spare_capacity(16 << 10);
                match r.try_read(spare) {
                    Ok(0) => {
                        core.handle_eof();
                        eof = true;
                    }
                    Ok(n) => core.read_buf().advance_end(n),
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                    Err(e) if e.kind() == std::io::ErrorKind::ConnectionReset => return Ok(()),
                    Err(e) => return Err(core.read_error(e, Instant::now().into_std()).into()),
                }
            }
            _ = tokio::time::sleep_until(deadline.map_or_else(Instant::now, Instant::from_std)),
                if deadline.is_some() => {
                core.handle_timeout(Instant::now().into_std());
            }
        }
    }
}

/// Handles an event, returning new downstreams to hand to the upstream task.
async fn handle_event(
    proxy: &Proxy,
    out: &Arc<ConnOut>,
    event: Event<'_, SetupStream>,
) -> Vec<(usize, Downstream)> {
    match event {
        Event::Describe(d) => {
            if d.url().and_then(|u| proxy.track_for_url(u)) != Some(None) {
                d.reject(StatusCode::NOT_FOUND);
                return Vec::new();
            }
            // Wait for every track to have a format; the upstream's SDP may
            // have omitted parameters, which then come in-band.
            let mut formats = Vec::with_capacity(proxy.tracks.len());
            for t in &proxy.tracks {
                let mut rx = t.format.clone();
                match tokio::time::timeout(DESCRIBE_TIMEOUT, rx.wait_for(Option::is_some)).await {
                    Ok(Ok(f)) => formats.push(f.clone().unwrap().format),
                    _ => {
                        d.reject(StatusCode::SERVICE_UNAVAILABLE);
                        return Vec::new();
                    }
                }
            }
            let media: Vec<_> = proxy
                .tracks
                .iter()
                .zip(&formats)
                .map(|(t, f)| SdpMedia {
                    format: f,
                    payload_type: t.payload_type,
                    control: &t.control,
                })
                .collect();
            d.respond(&retina::server::sdp("Retina proxy", &media));
            Vec::new()
        }
        Event::Setup(s) => {
            let Some(Some(track_i)) = proxy.track_for_url(s.url()) else {
                s.reject(StatusCode::NOT_FOUND);
                return Vec::new();
            };
            let sender = Sender::new(
                proxy.tracks[track_i].payload_type,
                rand::random(),
                rand::random(),
                rand::random(),
            );
            let ssrc = sender.ssrc();
            let id = s.accept(
                SetupStream {
                    track_i,
                    sender: Some(sender),
                    alive: Arc::new(AtomicBool::new(true)),
                },
                ssrc,
            );
            debug!("session {id}: set up track {track_i}");
            Vec::new()
        }
        Event::Play(mut p) => {
            let session = p.session();
            // Each repacketized track needs its current parameters.
            let packetizers: Option<Vec<_>> = p
                .streams()
                .iter()
                .map(|s| {
                    let track = &proxy.tracks[s.data.track_i];
                    match track.kind {
                        TrackKind::Repacketize => {
                            let f = track.format.borrow();
                            let params = f.as_ref()?.parameters.as_ref()?;
                            Some(Some(
                                retina::codec::VideoPacketizer::new(
                                    params,
                                    proxy.packetize_options,
                                )
                                .expect("H.264 or H.265 parameters"),
                            ))
                        }
                        TrackKind::Passthrough => Some(None),
                    }
                })
                .collect();
            let Some(packetizers) = packetizers else {
                p.reject(StatusCode::SERVICE_UNAVAILABLE);
                return Vec::new();
            };
            let mut joins = Vec::new();
            let mut rtp_info = Vec::new();
            for (s, packetizer) in p.streams_mut().iter_mut().zip(packetizers) {
                let sender = s.data.sender.take().expect("sender is taken only at PLAY");
                rtp_info.push(RtpInfo {
                    seq: Some(sender.next_sequence_number()),
                    rtptime: None,
                });
                joins.push((
                    s.data.track_i,
                    Downstream {
                        sender,
                        channel: s.channel,
                        conn: out.clone(),
                        alive: s.data.alive.clone(),
                        packetizer,
                        joined: false,
                    },
                ));
            }
            p.respond(&rtp_info);
            info!("session {session}: playing {} track(s)", joins.len());
            joins
        }
        Event::SessionClosed(c) => {
            info!("session {}: closed ({:?})", c.id, c.reason);
            for s in c.streams {
                s.data.alive.store(false, Ordering::Relaxed);
            }
            Vec::new()
        }
        _ => Vec::new(),
    }
}
