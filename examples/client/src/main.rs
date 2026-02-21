// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP client examples.

mod info;
mod jpeg;
mod mp4;
mod onvif;
mod webcodecs;

use anyhow::Error;
use clap::Parser;
use log::{error, info};
use tracing_subscriber::layer::SubscriberExt as _;

#[derive(Parser)]
struct Source {
    /// `rtsp://` URL to connect to.
    #[clap(long)]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[clap(long)]
    username: Option<String>,

    /// Password; requires username.
    #[clap(long, requires = "username")]
    password: Option<String>,
}

#[derive(Parser)]
enum Cmd {
    /// Gets info about available streams and exits.
    Info(info::Opts),
    /// Writes available audio and video streams to mp4 file; use Ctrl+C to stop.
    Mp4(mp4::Opts),
    /// Follows ONVIF metadata stream; use Ctrl+C to stop.
    Onvif(onvif::Opts),
    /// Writes depacketized JPEG images to disk; use CTRL+C to stop.
    Jpeg(jpeg::Opts),
    /// Serves a stream to a web browser via WebCodecs.
    Webcodecs(webcodecs::Opts),
}

fn init_logging() {
    let filter = tracing_subscriber::EnvFilter::builder()
        .with_default_directive(tracing_subscriber::filter::LevelFilter::INFO.into())
        .with_env_var("RUST_LOG")
        .from_env_lossy();
    tracing_log::LogTracer::init().unwrap();
    let sub = tracing_subscriber::registry()
        .with(
            tracing_subscriber::fmt::Layer::new()
                .with_writer(std::io::stderr)
                .with_thread_names(true),
        )
        .with(filter);
    tracing::subscriber::set_global_default(sub).unwrap();
}

#[tokio::main]
async fn main() {
    init_logging();
    if let Err(e) = { main_inner().await } {
        error!("Fatal: {}", itertools::join(e.chain(), "\ncaused by: "));
        std::process::exit(1);
    }
    info!("Done");
}

/// Interpets the `username` and `password` of a [Source].
fn creds(
    username: Option<String>,
    password: Option<String>,
) -> Option<retina::client::Credentials> {
    match (username, password) {
        (Some(username), password) => Some(retina::client::Credentials {
            username,
            password: password.unwrap_or_default(),
        }),
        (None, None) => None,
        _ => unreachable!(), // clap enforces that password requires username.
    }
}

async fn main_inner() -> Result<(), Error> {
    let cmd = Cmd::parse();
    match cmd {
        Cmd::Info(opts) => info::run(opts).await,
        Cmd::Jpeg(opts) => jpeg::run(opts).await,
        Cmd::Mp4(opts) => mp4::run(opts).await,
        Cmd::Onvif(opts) => onvif::run(opts).await,
        Cmd::Webcodecs(opts) => webcodecs::run(opts).await,
    }
}
