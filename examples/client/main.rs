// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTSP client examples.

mod metadata;
mod mp4;

use failure::Error;
use log::{error, info};
use std::{fmt::Write, str::FromStr};
use structopt::StructOpt;

#[derive(StructOpt)]
struct Source {
    #[structopt(long, parse(try_from_str))]
    url: url::Url,

    #[structopt(long, requires = "password")]
    username: Option<String>,

    #[structopt(long, requires = "username")]
    password: Option<String>,
}

#[derive(StructOpt)]
enum Cmd {
    Mp4(mp4::Opts),
    Metadata(metadata::Opts),
}

/// Returns a pretty-and-informative version of `e`.
pub fn prettify_failure(e: &failure::Error) -> String {
    let mut msg = e.to_string();
    for cause in e.iter_causes() {
        write!(&mut msg, "\ncaused by: {}", cause).unwrap();
    }
    if e.backtrace().is_empty() {
        write!(
            &mut msg,
            "\n\n(set environment variable RUST_BACKTRACE=1 to see backtraces)"
        )
        .unwrap();
    } else {
        write!(&mut msg, "\n\nBacktrace:\n{}", e.backtrace()).unwrap();
    }
    msg
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
        error!("Fatal: {}", prettify_failure(&e));
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
        (Some(username), Some(password)) => {
            Some(retina::client::Credentials { username, password })
        }
        (None, None) => None,
        _ => unreachable!(), // structopt/clap enforce username and password's mutual "requires".
    }
}

async fn main_inner() -> Result<(), Error> {
    let cmd = Cmd::from_args();
    match cmd {
        Cmd::Mp4(opts) => mp4::run(opts).await,
        Cmd::Metadata(opts) => metadata::run(opts).await,
    }
}
