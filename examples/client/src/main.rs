// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP client examples.

mod info;
mod mp4;
mod onvif;

use anyhow::Error;
use log::error;
use std::str::FromStr;
use structopt::StructOpt;

#[derive(StructOpt)]
struct Source {
    /// `rtsp://` URL to connect to.
    #[structopt(long, parse(try_from_str))]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[structopt(long)]
    username: Option<String>,

    /// Password; requires username.
    #[structopt(long, requires = "username")]
    password: Option<String>,
}

#[derive(StructOpt)]
enum Cmd {
    /// Gets info about available streams and exits.
    Info(info::Opts),
    /// Writes available audio and video streams to mp4 file; use Ctrl+C to stop.
    Mp4(mp4::Opts),
    /// Follows ONVIF metadata stream; use Ctrl+C to stop.
    Onvif(onvif::Opts),
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
        main_inner().await
    } {
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
        _ => unreachable!(), // structopt/clap enforce that password requires username.
    }
}

async fn main_inner() -> Result<(), Error> {
    let cmd = Cmd::from_args();
    match cmd {
        Cmd::Info(opts) => info::run(opts).await,
        Cmd::Mp4(opts) => mp4::run(opts).await,
        Cmd::Onvif(opts) => onvif::run(opts).await,
    }
}
