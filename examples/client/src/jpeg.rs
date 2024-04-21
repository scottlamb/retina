// Copyright (C) 2023 Niclas Olmenius <niclas@voysys.se>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Proof-of-concept `.jpeg` writer.
//!
//! This writes depacketized RTSP MJPEG images to a specified output directory.

use std::{num::NonZeroU32, path::PathBuf, pin::Pin, sync::Arc};

use anyhow::{anyhow, bail, Error};
use clap::Parser;
use futures::{Future, StreamExt};
use log::info;
use retina::{client::SetupOptions, codec::CodecItem};

#[derive(Parser)]
pub struct Opts {
    #[command(flatten)]
    src: super::Source,

    /// Policy for handling the `rtptime` parameter normally seem in the `RTP-Info` header.
    /// One of `default`, `require`, `ignore`, `permissive`.
    #[arg(default_value_t, long)]
    initial_timestamp: retina::client::InitialTimestampPolicy,

    /// Allow lost packets mid-stream without aborting.
    #[arg(long)]
    allow_loss: bool,

    /// When to issue a `TEARDOWN` request: `auto`, `always`, or `never`.
    #[arg(default_value_t, long)]
    teardown: retina::client::TeardownPolicy,

    /// Duration after which to exit automatically, in seconds.
    #[arg(long, name = "secs")]
    duration: Option<u64>,

    /// The transport to use: `tcp` or `udp` (experimental).
    ///
    /// Note: `--allow-loss` is strongly recommended with `udp`.
    #[arg(default_value_t, long)]
    transport: retina::client::Transport,

    /// Path to directory to write JPEG images.
    out_dir: PathBuf,
}

/// Writes `.jpeg` files to the specified directory.
async fn write_jpeg(
    opts: &Opts,
    session: retina::client::Session<retina::client::Described>,
    stop_signal: Pin<Box<dyn Future<Output = Result<(), std::io::Error>>>>,
) -> Result<(), Error> {
    let mut session = session
        .play(
            retina::client::PlayOptions::default()
                .initial_timestamp(opts.initial_timestamp)
                .enforce_timestamps_with_max_jump_secs(NonZeroU32::new(10).unwrap()),
        )
        .await?
        .demuxed()?;

    std::fs::create_dir_all(&opts.out_dir)?;

    let sleep = match opts.duration {
        Some(secs) => {
            futures::future::Either::Left(tokio::time::sleep(std::time::Duration::from_secs(secs)))
        }
        None => futures::future::Either::Right(futures::future::pending()),
    };
    tokio::pin!(stop_signal);
    tokio::pin!(sleep);

    let mut frame_count = 0;

    loop {
        tokio::select! {
            pkt = session.next() => {
                match pkt.ok_or_else(|| anyhow!("EOF"))?? {
                    CodecItem::VideoFrame(f) => {
                        let out_path = opts.out_dir.join(&format!("{frame_count:05}.jpeg"));
                        std::fs::write(out_path, f.data())?;

                        frame_count += 1;
                    },
                    CodecItem::Rtcp(rtcp) => {
                        if let (Some(t), Some(Ok(Some(sr)))) = (rtcp.rtp_timestamp(), rtcp.pkts().next().map(retina::rtcp::PacketRef::as_sender_report)) {
                            println!("{}: SR ts={}", t, sr.ntp_timestamp());
                        }
                    },
                    _ => continue,
                };
            },
            _ = &mut stop_signal => {
                info!("Stopping due to signal");
                break;
            },
            _ = &mut sleep => {
                info!("Stopping after {} seconds", opts.duration.unwrap());
                break;
            },
        }
    }

    Ok(())
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    let creds = super::creds(opts.src.username.clone(), opts.src.password.clone());
    let stop_signal = Box::pin(tokio::signal::ctrl_c());
    let session_group = Arc::new(retina::client::SessionGroup::default());
    let mut session = retina::client::Session::describe(
        opts.src.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .session_group(session_group.clone())
            .user_agent("Retina jpeg example".to_owned())
            .teardown(opts.teardown),
    )
    .await?;
    let video_stream_i = {
        let s = session.streams().iter().position(|s| {
            if s.media() == "image" || s.media() == "video" {
                if s.encoding_name() == "jpeg" {
                    log::info!("Using jpeg video stream");
                    return true;
                }
                log::info!(
                    "Ignoring {} video stream because it's unsupported",
                    s.encoding_name(),
                );
            }
            false
        });
        if s.is_none() {
            log::info!("No suitable video stream found");
        }
        s
    };

    if let Some(i) = video_stream_i {
        session
            .setup(i, SetupOptions::default().transport(opts.transport.clone()))
            .await?;
    }
    if video_stream_i.is_none() {
        bail!("Exiting because no video or audio stream was selected; see info log messages above");
    }

    let result = write_jpeg(&opts, session, stop_signal).await;

    // Session has now been dropped, on success or failure. A TEARDOWN should
    // be pending if necessary. session_group.await_teardown() will wait for it.
    if let Err(e) = session_group.await_teardown().await {
        log::error!("TEARDOWN failed: {}", e);
    }
    result
}
