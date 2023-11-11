// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use anyhow::{anyhow, bail, Error};
use clap::Parser;
use futures::StreamExt;
use log::{error, info};
use retina::{
    client::SetupOptions,
    codec::{CodecItem, VideoFrame},
};
use std::{str::FromStr, sync::Arc};
use webrtc::{
    api::{interceptor_registry::register_default_interceptors, APIBuilder},
    ice_transport::{ice_connection_state::RTCIceConnectionState, ice_server::RTCIceServer},
    interceptor::registry::Registry,
    media::Sample,
    peer_connection::{
        configuration::RTCConfiguration, peer_connection_state::RTCPeerConnectionState,
        sdp::session_description::RTCSessionDescription,
    },
    rtp_transceiver::rtp_codec::RTCRtpCodecCapability,
    track::track_local::{track_local_static_sample::TrackLocalStaticSample, TrackLocal},
};

/// Proxies from the given RTSP server to a WebRTC client.
///
/// This currently uses a jsfiddle borrowed from
/// [webrtc-rs](https://github.com/webrtc-rs/webrtc)'s examples which expects
/// you to help out the negotiation by pasting the browser's offer (as a long
/// base64 string) to the CLI, then the CLI's answer back in the same manner. It
/// also only supports a single client.
///
/// A future version might embed a webserver so you can just go to the supplied
/// URL and have everything work.
#[derive(Parser)]
struct Opts {
    /// `rtsp://` URL to connect to.
    #[arg(long)]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[arg(long)]
    username: Option<String>,

    /// Password; requires username.
    #[arg(long, requires = "username")]
    password: Option<String>,

    /// When to issue a `TEARDOWN` request: `auto`, `always`, or `never`.
    #[arg(default_value_t, long)]
    teardown: retina::client::TeardownPolicy,

    /// The transport to use: `tcp` or `udp` (experimental).
    #[arg(default_value_t, long)]
    transport: retina::client::Transport,
}

fn init_logging() -> mylog::Handle {
    let h = mylog::Builder::new()
        .set_format(
            ::std::env::var("MOONFIRE_FORMAT")
                .map_err(|_| ())
                .and_then(|s| mylog::Format::from_str(&s))
                .unwrap_or(mylog::Format::Google),
        )
        .set_spec(::std::env::var("MOONFIRE_LOG").as_deref().unwrap_or("info"))
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
        error!("{}", e);
        std::process::exit(1);
    }
}

fn read_offer() -> Result<RTCSessionDescription, Error> {
    // Avoid <https://github.com/webrtc-rs/examples/issues/16> by using rustyline
    // to take the terminal out of canonical mode.
    let mut rl = rustyline::Editor::<()>::new();
    let line = rl.readline(">> ")?;
    let line = line.trim();
    let raw = base64::decode(line)?;
    Ok(serde_json::from_slice(&raw)?)
}

async fn run() -> Result<(), Error> {
    let opts = Opts::parse();
    let creds = match (opts.username, opts.password) {
        (Some(username), password) => Some(retina::client::Credentials {
            username,
            password: password.unwrap_or_default(),
        }),
        (None, None) => None,
        _ => unreachable!(), // structopt/clap enforce that password requires username.
    };
    let stop_signal = tokio::signal::ctrl_c();
    tokio::pin!(stop_signal);
    let upstream_session_group = Arc::new(retina::client::SessionGroup::default());
    let mut upstream_session = retina::client::Session::describe(
        opts.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .session_group(upstream_session_group.clone())
            .user_agent("Retina webrtc-proxy example".to_owned())
            .teardown(opts.teardown),
    )
    .await?;

    let mut m = webrtc::api::media_engine::MediaEngine::default();
    m.register_default_codecs()?;

    // Create a InterceptorRegistry. This is the user configurable RTP/RTCP Pipeline.
    // This provides NACKs, RTCP Reports and other features. If you use `webrtc.NewPeerConnection`
    // this is enabled by default. If you are manually managing You MUST create a InterceptorRegistry
    // for each PeerConnection.
    let mut registry = Registry::new();

    // Use the default set of Interceptors
    registry = register_default_interceptors(registry, &mut m)?;

    // Create the API object with the MediaEngine
    let api = APIBuilder::new()
        .with_media_engine(m)
        .with_interceptor_registry(registry)
        .build();

    // Prepare the configuration
    let downstream_cfg = RTCConfiguration {
        ice_servers: vec![RTCIceServer {
            urls: vec!["stun:stun.l.google.com:19302".to_owned()],
            ..Default::default()
        }],
        ..Default::default()
    };

    let downstream_conn = Arc::new(api.new_peer_connection(downstream_cfg).await?);
    let mut tracks = Vec::new();

    // Prepare outbound state for each track of interest.
    for (i, stream) in upstream_session.streams().iter().enumerate() {
        if stream.media() != "video" && stream.encoding_name() != "h264" {
            // Currently we only support H.264 video.
            continue;
        }

        // This could work in a few different ways:
        //
        // 1. Pass RTP packets from upstream to downstream unmodified. (From
        //    retina::client::Session's Stream impl to
        //    webrtc::track::track_local::track_local_static_rtp::TrackLocalStaticRtp.)
        //    This only works if the upstream and downstream agree on an
        //    acceptable MTU.
        // 2. Pass whole frames (aka samples or H.264 access units). (From
        //    retina::client::Demuxed's Stream impl to
        //    webrtc::track::track_local::track_local_static_sample::TrackLocalStaticSample.)
        //    This introduces a slight lag if it takes a long time to receive a
        //    complete frame from upstream.
        // 3. Repacketize on-the-fly, buffering upstream packets and flushing
        //    every downstream MTU, buffering at most
        //    max(upstream MTU, downstream MTU) bytes.
        //
        // #3 seems ideal but is not yet implemented. The current approach is #2.
        let track = Arc::new(TrackLocalStaticSample::new(
            RTCRtpCodecCapability {
                mime_type: "video/h264".to_owned(),
                ..Default::default()
            },
            format!("{i}-video"),
            "retina-webrtc-proxy".to_owned(),
        ));
        let sender = downstream_conn
            .add_track(Arc::clone(&track) as Arc<dyn TrackLocal + Send + Sync>)
            .await?;

        // Read incoming RTCP packets
        // Before these packets are returned they are processed by interceptors. For things
        // like NACK this needs to be called.
        tokio::spawn(async move {
            let mut rtcp_buf = vec![0u8; 1500];
            while let Ok((_, _)) = sender.read(&mut rtcp_buf).await {}
        });

        if tracks.len() <= i {
            tracks.resize(i + 1, None);
        }
        tracks[i] = Some(track);
    }

    // Set up the streams on the inbound side.
    for i in tracks
        .iter()
        .enumerate()
        .filter_map(|(i, track)| track.as_ref().map(|_| i))
    {
        upstream_session
            .setup(i, SetupOptions::default().transport(opts.transport.clone()))
            .await?;
    }

    let mut upstream_session = upstream_session
        .play(retina::client::PlayOptions::default())
        .await?
        .demuxed()?;

    // Set the handler for ICE connection state
    // This will notify you when the peer has connected/disconnected
    let (ice_conn_state_tx, ice_conn_state_rx) = tokio::sync::mpsc::unbounded_channel();
    downstream_conn
        .on_ice_connection_state_change(Box::new(move |state: RTCIceConnectionState| {
            ice_conn_state_tx.send(state).unwrap();
            Box::pin(async {})
        }))
        .await;
    tokio::pin!(ice_conn_state_rx);
    let (peer_conn_state_tx, peer_conn_state_rx) = tokio::sync::mpsc::unbounded_channel();
    downstream_conn
        .on_peer_connection_state_change(Box::new(move |state: RTCPeerConnectionState| {
            peer_conn_state_tx.send(state).unwrap();
            Box::pin(async {})
        }))
        .await;
    tokio::pin!(peer_conn_state_rx);

    println!("Navigate to https://jsfiddle.net/9s10amwL/ in your browser.");
    println!("Paste from the 'Browser base64 Session description' box to here:");
    let offer = read_offer()?;
    println!();
    downstream_conn.set_remote_description(offer).await?;
    let answer = downstream_conn.create_answer(None).await?;
    downstream_conn.set_local_description(answer).await?;
    downstream_conn
        .gathering_complete_promise()
        .await
        .recv()
        .await;
    if let Some(local_desc) = downstream_conn.local_description().await {
        println!("Paste from here to the 'Golang base64 Session Description' box:");
        println!("{}", base64::encode(serde_json::to_string(&local_desc)?));
    } else {
        bail!("downstream_conn has no local_description");
    }

    loop {
        tokio::select! {
            item = upstream_session.next() => {
                match item {
                    Some(Ok(CodecItem::VideoFrame(f))) => {
                        if let Some(t) = tracks.get(f.stream_id()).and_then(Option::as_ref) {
                            t.write_sample(&Sample {
                                data: convert_h264(f)?.into(),

                                // TODO: webrtc-rs appears to calculate the
                                // timestamp from this frame's duration:
                                // https://github.com/webrtc-rs/webrtc/blob/7681d923f216e281f86ca6e453529b9853eeceab/src/track/track_local/track_local_static_sample.rs#L65
                                // https://github.com/webrtc-rs/rtp/blob/ef3be6febc7d4b261c2ad991cb4e467bb80ccce0/src/packetizer/mod.rs#L137
                                // which is wrong and unknowable without lagging
                                // a frame. The timestamp really should be based
                                // on time elapsed since the *previous* frame;
                                // maybe supply that here...
                                duration: tokio::time::Duration::from_secs(1),
                                ..Default::default()
                            }).await?;
                        }
                    },
                    Some(Ok(_)) => {},
                    Some(Err(e)) => {
                        return Err(anyhow!(e).context("upstream failure"));
                    }
                    None => {
                        info!("upstream EOF");
                        return Ok(());
                    }
                }
            },
            state = ice_conn_state_rx.recv() => {
                let state = state.unwrap();
                info!("ice conn state: {:?}", state);
            },
            state = peer_conn_state_rx.recv() => {
                let state = state.unwrap();
                info!("peer conn state: {:?}", state);
                if matches!(state, RTCPeerConnectionState::Failed) {
                    return Ok(());
                }
            },
            _ = &mut stop_signal => {
                info!("received ctrl-C");
                break;
            },
        }
    }

    Ok(())
}

/// Converts from AVC representation to the Annex B representation expected by webrtc-rs.
fn convert_h264(frame: VideoFrame) -> Result<Vec<u8>, Error> {
    // TODO:
    // * For each IDR frame, copy the SPS and PPS from the stream's
    //   parameters, rather than depend on it being present in the frame
    //   already. In-band parameters aren't guaranteed. This is awkward
    //   with h264_reader v0.5's h264_reader::avcc::AvcDecoderRecord because it
    //   strips off the NAL header byte from each parameter. The next major
    //   version shouldn't do this.
    // * Copy only the slice data. In particular, don't copy SEI, which confuses
    //   Safari: <https://github.com/scottlamb/retina/issues/60#issuecomment-1178369955>

    let mut data = frame.into_data();
    let mut i = 0;
    while i < data.len() - 3 {
        // Replace each NAL's length with the Annex B start code b"\x00\x00\x00\x01".
        let len = u32::from_be_bytes([data[i], data[i + 1], data[i + 2], data[i + 3]]) as usize;
        data[i] = 0;
        data[i + 1] = 0;
        data[i + 2] = 0;
        data[i + 3] = 1;
        i += 4 + len;
        if i > data.len() {
            bail!("partial NAL body");
        }
    }
    if i < data.len() {
        bail!("partial NAL length");
    }
    Ok(data)
}
