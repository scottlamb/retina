// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A downstream RTSP connection: a tokio driver around
//! [`retina::server::ConnectionCore`].

use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::time::Duration;

use anyhow::Error;
use retina::codec::VideoPacketizer;
use retina::rtp::{Sender, SenderOptions};
use retina::rtsp::msg::StatusCode;
use retina::server::{
    ConnectionCore, Describe, Event, Pending, Play, RtpInfo, SdpMedia, ServerOptions,
};
use tokio::time::Instant;
use tracing::{Instrument as _, debug, info};

use crate::fanout::{ConnOut, Downstream};
use crate::{Proxy, Track, TrackFormat, TrackKind};

/// How long `DESCRIBE` and `PLAY` wait for the upstream to supply codec
/// parameters.
const FORMAT_TIMEOUT: Duration = Duration::from_secs(10);

/// The proxy's data for each stream set up within a session.
struct SetupStream {
    track_i: usize,
    sender: Option<Sender>,
    alive: Arc<AtomicBool>,
}

/// The result of a request's asynchronous work, to apply to the core.
enum Answer {
    Describe(Pending<Describe>, Result<String, StatusCode>),

    /// For each of the session's streams, its packetizer if repacketized.
    Play(
        Pending<Play>,
        Result<Vec<Option<VideoPacketizer>>, StatusCode>,
    ),
}

/// Asynchronous work for the outstanding request. It borrows only the
/// `Proxy`, not the core, so the read loop keeps driving the core meanwhile.
type AnswerFuture<'a> = Pin<Box<dyn Future<Output = Answer> + Send + 'a>>;

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
    for s in core.into_sessions() {
        for st in s.streams {
            out.stop(&st.data.alive);
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
    let mut answer: Option<AnswerFuture<'_>> = None;
    loop {
        // While a request is outstanding, this still handles interleaved
        // data and session timeouts.
        while let Some(event) = core.poll_event(Instant::now().into_std()) {
            if let Some(f) = handle_event(proxy, core, out, event?) {
                debug_assert!(answer.is_none());
                answer = Some(f);
            }
        }
        write_transmit(core, out);
        if eof || out.is_closed() {
            if answer.is_some() {
                debug!(
                    conn = %core.conn_ctx(),
                    "closed; abandoning outstanding request"
                );
            }
            return Ok(());
        }
        let deadline = core.poll_timeout();
        tokio::select! {
            readable = r.readable(), if core.wants_read() => {
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
            a = async { answer.as_mut().expect("answer is some").await }, if answer.is_some() => {
                answer = None;
                let joins = apply_answer(proxy, core, out, a);

                // Write the response before the new downstreams' first packets.
                write_transmit(core, out);
                for (track_i, d) in joins {
                    // The upstream task only goes away on error, which ends the process.
                    let _ = proxy.tracks[track_i].joins.send(d);
                }
            }
            else => {
                // Not reading only while a request is outstanding, which
                // implies `answer` is some.
                unreachable!("nothing to wait for");
            }
        }
    }
}

/// Moves `core`'s responses into `out`, after any data packets already there.
fn write_transmit(core: &mut ConnectionCore<SetupStream>, out: &ConnOut) {
    let (first, second) = core.transmit_buf();
    if first.is_empty() {
        return;
    }
    let n = first.len() + second.len();
    out.write_rtsp((first, second));
    core.advance_transmit(n);
}

/// Handles an event, answering it now or returning the work to answer it.
fn handle_event<'a>(
    proxy: &'a Proxy,
    core: &mut ConnectionCore<SetupStream>,
    out: &ConnOut,
    event: Event<SetupStream>,
) -> Option<AnswerFuture<'a>> {
    match event {
        Event::Describe(d) => {
            if d.url().and_then(|u| proxy.track_for_url(u)) != Some(None) {
                core.respond_describe(d, Err(StatusCode::NOT_FOUND));
                return None;
            }
            let span = d.span().clone();
            Some(Box::pin(
                async move {
                    let r = describe(proxy).await;
                    Answer::Describe(d, r)
                }
                .instrument(span),
            ))
        }
        Event::Setup(s) => {
            let Some(Some(track_i)) = proxy.track_for_url(s.url()) else {
                let _ = core.respond_setup(s, Err(StatusCode::NOT_FOUND));
                return None;
            };
            let sender = Sender::new(
                proxy.tracks[track_i].payload_type,
                SenderOptions::default().max_payload_size(proxy.max_payload_size),
            );
            let ssrc = sender.ssrc();
            let data = SetupStream {
                track_i,
                sender: Some(sender),
                alive: Arc::new(AtomicBool::new(true)),
            };
            if let Ok(id) = core.respond_setup(s, Ok((data, ssrc))) {
                debug!(session_id = %id, track = track_i, "set up track");
            }
            None
        }
        Event::Play(p) => {
            let track_is: Vec<usize> = core
                .streams(p.session_id())
                .expect("session of outstanding PLAY exists")
                .iter()
                .map(|s| s.data.track_i)
                .collect();
            let span = p.span().clone();
            Some(Box::pin(
                async move {
                    let r = play_packetizers(proxy, &track_is).await;
                    Answer::Play(p, r)
                }
                .instrument(span),
            ))
        }
        Event::Teardown(t) => {
            // Stop the streams before responding, so no packet follows the
            // response on channels a later `SETUP` might reuse.
            let session = t.session_id();
            for s in core.streams(session).into_iter().flatten() {
                out.stop(&s.data.alive);
            }
            if core.respond_teardown(t).is_ok() {
                info!(session_id = %session, "torn down");
            }
            None
        }
        Event::SessionTimedOut(c) => {
            info!(session_id = %c.id, "timed out");
            for s in c.streams {
                out.stop(&s.data.alive);
            }
            None
        }
        _ => None,
    }
}

/// Waits for `track` to have a format; the upstream's SDP may have omitted
/// parameters, which then come in-band.
async fn wait_format(track: &Track) -> Result<TrackFormat, StatusCode> {
    let mut rx = track.format.clone();
    match tokio::time::timeout(FORMAT_TIMEOUT, rx.wait_for(Option::is_some)).await {
        Ok(Ok(f)) => Ok(f.clone().expect("format is some")),
        _ => Err(StatusCode::SERVICE_UNAVAILABLE),
    }
}

async fn describe(proxy: &Proxy) -> Result<String, StatusCode> {
    let mut formats = Vec::with_capacity(proxy.tracks.len());
    for t in &proxy.tracks {
        formats.push(wait_format(t).await?.format);
    }
    let media: Vec<_> = proxy
        .tracks
        .iter()
        .zip(&formats)
        .map(|(t, f)| SdpMedia::new(f, t.payload_type, &t.control))
        .collect();
    Ok(retina::server::sdp("Retina proxy", &media))
}

/// Returns a packetizer for each repacketized track, with its current parameters.
async fn play_packetizers(
    proxy: &Proxy,
    track_is: &[usize],
) -> Result<Vec<Option<VideoPacketizer>>, StatusCode> {
    let mut packetizers = Vec::with_capacity(track_is.len());
    for &i in track_is {
        let track = &proxy.tracks[i];
        packetizers.push(match track.kind {
            TrackKind::Repacketize => {
                let f = wait_format(track).await?;
                let params = f
                    .parameters
                    .as_ref()
                    .ok_or(StatusCode::SERVICE_UNAVAILABLE)?;
                Some(
                    VideoPacketizer::new(params, proxy.packetize_options)
                        .expect("H.264 or H.265 parameters"),
                )
            }
            TrackKind::Passthrough => None,
        });
    }
    Ok(packetizers)
}

/// Applies an answer to the core, returning new downstreams to hand to the
/// upstream task once the response is written.
fn apply_answer(
    proxy: &Proxy,
    core: &mut ConnectionCore<SetupStream>,
    out: &Arc<ConnOut>,
    answer: Answer,
) -> Vec<(usize, Downstream)> {
    match answer {
        Answer::Describe(d, r) => {
            core.respond_describe(d, r.as_deref().map_err(|&s| s));
            Vec::new()
        }
        Answer::Play(p, Err(status)) => {
            let _ = core.respond_play(p, Err(status));
            Vec::new()
        }
        Answer::Play(p, Ok(packetizers)) => {
            let session = p.session_id();
            let Some(streams) = core.streams_mut(session) else {
                let _ = core.respond_play(p, Err(StatusCode::SESSION_NOT_FOUND));
                return Vec::new();
            };
            let mut joins = Vec::new();
            let mut rtp_info = Vec::new();
            for (s, packetizer) in streams.iter_mut().zip(packetizers) {
                let sender = s.data.sender.take().expect("sender is taken only at PLAY");
                rtp_info.push(RtpInfo {
                    seq: Some(sender.next_sequence_number()),
                    rtptime: None,
                });
                joins.push((
                    s.data.track_i,
                    Downstream::new(
                        sender,
                        s.channel,
                        out.clone(),
                        proxy.cname.clone(),
                        s.data.alive.clone(),
                        packetizer,
                    ),
                ));
            }
            if core.respond_play(p, Ok(&rtp_info)).is_err() {
                return Vec::new();
            }
            info!(session_id = %session, "playing {} track(s)", joins.len());
            joins
        }
    }
}
