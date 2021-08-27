// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use anyhow::{anyhow, Error};
use futures::StreamExt;
use log::info;
use retina::codec::CodecItem;

#[derive(structopt::StructOpt)]
pub struct Opts {
    #[structopt(flatten)]
    src: super::Source,
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    let stop = tokio::signal::ctrl_c();

    let creds = super::creds(opts.src.username, opts.src.password);
    let mut session = retina::client::Session::describe(
        opts.src.url,
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina metadata example".to_owned()),
    )
    .await?;
    let onvif_stream_i = session
        .streams()
        .iter()
        .position(|s| matches!(s.parameters(), Some(retina::codec::Parameters::Message(..))))
        .ok_or_else(|| anyhow!("couldn't find onvif stream"))?;
    session.setup(onvif_stream_i).await?;
    let mut session = session
        .play(retina::client::PlayOptions::default().ignore_zero_seq(true))
        .await?
        .demuxed()?;

    tokio::pin!(stop);
    loop {
        tokio::select! {
            item = session.next() => {
                match item.ok_or_else(|| anyhow!("EOF"))?? {
                    CodecItem::MessageFrame(m) => {
                        info!("{}: {}\n", &m.timestamp, std::str::from_utf8(&m.data[..]).unwrap());
                    },
                    _ => continue,
                };
            },
            _ = &mut stop => {
                break;
            },
        }
    }
    session.teardown().await?;
    Ok(())
}
