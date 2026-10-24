// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A repacketizing RTSP proxy.
//!
//! Connects to one upstream RTSP server and serves its stream to any number of
//! downstream RTSP clients, over RTP/AVP/TCP (interleaved) only. H.264 and
//! H.265 video is depacketized once and repacketized for each downstream, so
//! downstreams get RFC-clean packets of the chosen size regardless of upstream
//! quirks, and a slow downstream is throttled at frame boundaries without
//! affecting the others. Other streams (e.g. audio) are passed through packet
//! by packet.

mod conn;
mod fanout;

use std::str::FromStr as _;
use std::sync::Arc;

use anyhow::{Error, bail};
use clap::Parser;
use log::{error, info, warn};
use retina::client::{PlayingItem, SetupOptions};
use retina::codec::{Depacketizer, PayloadFormat, VideoPacketizerOptions};
use url::Url;

use fanout::{Downstream, TrackFormat, UpstreamKind, UpstreamTrack, WallClock};

#[derive(Parser)]
struct Opts {
    /// Upstream `rtsp://` URL to connect to.
    #[arg(long)]
    url: Url,

    /// Username to send if the upstream server requires authentication.
    #[arg(long)]
    username: Option<String>,

    /// Password; requires username.
    #[arg(long, requires = "username")]
    password: Option<String>,

    /// The upstream transport: `tcp` or `udp` (experimental).
    #[arg(default_value_t, long)]
    transport: retina::client::Transport,

    /// Address to accept downstream connections on.
    #[arg(long, default_value = "0.0.0.0:8554")]
    listen: std::net::SocketAddr,

    /// Path to serve the stream at, e.g. `rtsp://host:8554/stream`.
    #[arg(long, default_value = "stream")]
    path: String,

    /// Maximum RTP payload size of repacketized video, in bytes.
    #[arg(long, default_value_t = 1400)]
    max_payload_size: u16,
}

enum TrackKind {
    Repacketize,
    Passthrough,
}

/// A stream being proxied, as seen by downstream connections.
struct Track {
    kind: TrackKind,
    payload_type: u8,

    /// The control URL, relative to `rtsp://host/path/`.
    control: String,

    /// The current format, once known.
    format: tokio::sync::watch::Receiver<Option<TrackFormat>>,

    /// Where to send new downstreams, to be picked up by the upstream task.
    joins: tokio::sync::mpsc::UnboundedSender<Downstream>,
}

struct Proxy {
    path: String,
    tracks: Vec<Track>,
    packetize_options: VideoPacketizerOptions,

    /// The maximum RTP payload size of repacketized video, for each
    /// downstream's [`retina::rtp::Sender`].
    max_payload_size: u16,

    /// The RTCP `CNAME` of every stream the proxy sends. One is shared so
    /// receivers can synchronize the tracks with each other.
    cname: Arc<str>,
}

impl Proxy {
    /// Maps a request URL to `Some(None)` for the presentation,
    /// `Some(Some(i))` for track `i`, or `None`.
    fn track_for_url(&self, url: &Url) -> Option<Option<usize>> {
        let path = url.path().trim_matches('/');
        let rest = path.strip_prefix(self.path.as_str())?;
        if rest.is_empty() {
            return Some(None);
        }
        let control = rest.strip_prefix('/')?;
        self.tracks
            .iter()
            .position(|t| t.control == control)
            .map(Some)
    }
}

fn init_logging() -> mylog::Handle {
    let h = mylog::Builder::new()
        .format(
            ::std::env::var("RUST_FORMAT")
                .map_err(|_| ())
                .and_then(|s| mylog::Format::from_str(&s))
                .unwrap_or(mylog::Format::Google),
        )
        .spec(::std::env::var("RUST_LOG").as_deref().unwrap_or("info"))
        .build();
    h.clone().install().unwrap();
    h
}

#[tokio::main]
async fn main() {
    let mut h = init_logging();
    if let Err(e) = {
        let _a = h.async_scope();
        run().await
    } {
        error!("{e}");
        std::process::exit(1);
    }
}

async fn run() -> Result<(), Error> {
    let opts = Opts::parse();
    let packetize_options = VideoPacketizerOptions::default();
    let (tracks, session, upstream) = setup_rtsp(&opts, &opts.url).await?;
    let upstream = run_upstream(session, upstream);
    let proxy = Arc::new(Proxy {
        path: opts.path.trim_matches('/').to_owned(),
        tracks,
        packetize_options,
        max_payload_size: opts.max_payload_size,
        cname: retina::rtcp::random_cname().into(),
    });
    let listener = tokio::net::TcpListener::bind(opts.listen).await?;
    info!(
        "serving at rtsp://{}/{}",
        listener.local_addr()?,
        proxy.path
    );
    tokio::select! {
        r = upstream => r,
        r = accept(listener, proxy) => r,
        _ = tokio::signal::ctrl_c() => {
            info!("exiting on ctrl-c");
            Ok(())
        }
    }
}

/// Creates a track, returning the downstream and upstream halves.
fn new_track(
    kind: TrackKind,
    track_i: usize,
    payload_type: u8,
    upstream_kind: UpstreamKind,
    format: Option<TrackFormat>,
) -> (Track, UpstreamTrack) {
    let (format_tx, format_rx) = tokio::sync::watch::channel(format);
    let (joins_tx, joins_rx) = tokio::sync::mpsc::unbounded_channel();
    (
        Track {
            kind,
            payload_type,
            control: format!("trackID={track_i}"),
            format: format_rx,
            joins: joins_tx,
        },
        UpstreamTrack {
            kind: upstream_kind,
            downstreams: Vec::new(),
            joins: joins_rx,
            format: format_tx,
            wall_clock: None,
        },
    )
}

/// Connects to the upstream RTSP server and starts playing.
async fn setup_rtsp(
    opts: &Opts,
    url: &Url,
) -> Result<
    (
        Vec<Track>,
        retina::client::Session<retina::client::Playing>,
        Vec<Option<UpstreamTrack>>,
    ),
    Error,
> {
    let creds = opts
        .username
        .clone()
        .map(|username| retina::client::Credentials {
            username,
            password: opts.password.clone().unwrap_or_default(),
        });
    let mut session = retina::client::Session::describe(
        url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina proxy example".to_owned()),
    )
    .await?;

    // Choose streams: H.264 and H.265 video is repacketized; other video and
    // audio are passed through.
    let chosen: Vec<(usize, TrackKind)> = session
        .streams()
        .iter()
        .enumerate()
        .filter_map(|(i, s)| match (s.media(), s.encoding_name()) {
            ("video", "h264" | "h265") => Some((i, TrackKind::Repacketize)),
            ("video" | "audio", _) => Some((i, TrackKind::Passthrough)),
            (m, e) => {
                info!("skipping upstream stream {i}: {m}/{e}");
                None
            }
        })
        .collect();
    if chosen.is_empty() {
        bail!("no supported upstream streams");
    }
    for (i, _) in &chosen {
        session
            .setup(
                *i,
                SetupOptions::default().transport(opts.transport.clone()),
            )
            .await?;
    }

    let mut tracks = Vec::new();
    let mut upstream: Vec<Option<UpstreamTrack>> =
        (0..session.streams().len()).map(|_| None).collect();
    for (track_i, (stream_i, kind)) in chosen.into_iter().enumerate() {
        let stream = &session.streams()[stream_i];
        let (upstream_kind, format) = match kind {
            TrackKind::Repacketize => {
                let Depacketizer::Video(d) = stream.new_depacketizer().map_err(Error::msg)? else {
                    bail!("expected a video depacketizer for stream {stream_i}");
                };
                let format = d.parameters().map(TrackFormat::video);
                (UpstreamKind::Video(d), format)
            }
            TrackKind::Passthrough => {
                // As is conventional in SDP, use an uppercase encoding name.
                let f = stream.payload_format();
                let mut format = PayloadFormat::new(
                    f.media().to_owned(),
                    f.encoding_name().to_ascii_uppercase(),
                    f.clock_rate(),
                );
                if let Some(c) = f.channels() {
                    format = format.with_channels(c);
                }
                if let Some(fmtp) = f.fmtp() {
                    format = format.with_fmtp(fmtp);
                }
                (
                    UpstreamKind::Passthrough,
                    Some(TrackFormat {
                        format,
                        parameters: None,
                    }),
                )
            }
        };
        let (track, up) = new_track(
            kind,
            track_i,
            stream.rtp_payload_type(),
            upstream_kind,
            format,
        );
        tracks.push(track);
        upstream[stream_i] = Some(up);
    }
    let session = session.play(retina::client::PlayOptions::default()).await?;
    Ok((tracks, session, upstream))
}

async fn accept(listener: tokio::net::TcpListener, proxy: Arc<Proxy>) -> Result<(), Error> {
    loop {
        let (stream, peer) = listener.accept().await?;
        info!("{peer}: connected");
        let proxy = proxy.clone();
        tokio::spawn(async move {
            match conn::serve(proxy, stream).await {
                Ok(()) => info!("{peer}: closed"),
                Err(e) => warn!("{peer}: {e}"),
            }
        });
    }
}

async fn run_upstream(
    mut session: retina::client::Session<retina::client::Playing>,
    mut tracks: Vec<Option<UpstreamTrack>>,
) -> Result<(), Error> {
    while let Some(item) = session.next_item().await {
        match item? {
            PlayingItem::Rtp(pkt) => {
                if let Some(t) = &mut tracks[pkt.stream_id()] {
                    t.push(pkt.packet());
                }
            }
            PlayingItem::Rtcp(rtcp) => {
                let Some(t) = &mut tracks[rtcp.stream_id()] else {
                    continue;
                };
                let Some(timestamp) = rtcp.rtp_timestamp() else {
                    continue;
                };
                let sr = rtcp
                    .pkts()
                    .find_map(|p| p.as_sender_report().ok().flatten());
                if let Some(sr) = sr {
                    t.set_wall_clock(WallClock {
                        ntp: sr.ntp_timestamp(),
                        timestamp,
                        at: rtcp.ctx().received(),
                    });
                }
            }
            _ => {}
        }
    }
    bail!("upstream ended");
}
