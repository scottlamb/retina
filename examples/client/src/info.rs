// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Gets info about available streams and exits.

use anyhow::Error;
use clap::Parser;

#[derive(Parser)]
pub struct Opts {
    #[command(flatten)]
    src: super::Source,

    /// Prints the SDP (Session Description Protocol) session description.
    #[arg(long)]
    print_sdp: bool,

    /// Prints debug output for each decoded stream.
    #[arg(long)]
    print_streams: bool,
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    let creds = super::creds(opts.src.username.clone(), opts.src.password.clone());
    let session = retina::client::Session::describe(
        opts.src.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina sdp example".to_owned()),
    )
    .await?;
    if opts.print_sdp {
        println!("SDP:\n{}\n\n", std::str::from_utf8(session.sdp())?);
    }
    if opts.print_streams {
        for (i, stream) in session.streams().iter().enumerate() {
            println!("stream {i}:\n{stream:#?}\n\n");
        }
    }
    if !opts.print_sdp && !opts.print_streams {
        eprintln!("You probably wanted at least one of --print-sdp or --print-streams?");
    }
    Ok(())
}
