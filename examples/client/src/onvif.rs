// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use anyhow::{Error, anyhow};
use clap::Parser;
use log::{error, info};
use retina::client::{SessionGroup, SetupOptions};

use crate::demux::{Demuxer, Item};
use std::sync::Arc;

#[derive(Parser)]
pub struct Opts {
    #[command(flatten)]
    src: super::Source,
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    let session_group = Arc::new(SessionGroup::default());
    let r = run_inner(opts, session_group.clone()).await;
    if let Err(e) = session_group.await_teardown().await {
        error!("TEARDOWN failed: {}", e);
    }
    r
}

async fn run_inner(opts: Opts, session_group: Arc<SessionGroup>) -> Result<(), Error> {
    let stop = tokio::signal::ctrl_c();

    let creds = super::creds(opts.src.username, opts.src.password);
    let mut session = retina::client::Session::describe(
        opts.src.url,
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina metadata example".to_owned())
            .session_group(session_group),
    )
    .await?;
    let onvif_stream_i = session
        .streams()
        .iter()
        .position(|s| {
            matches!(
                s.parameters(),
                Some(retina::codec::ParametersRef::Message(..))
            )
        })
        .ok_or_else(|| anyhow!("couldn't find onvif stream"))?;
    session
        .setup(onvif_stream_i, SetupOptions::default())
        .await?;
    let mut session = session.play(retina::client::PlayOptions::default()).await?;
    let mut demuxer = Demuxer::new(&session, retina::codec::FrameFormat::default())?;

    tokio::pin!(stop);
    loop {
        tokio::select! {
            item = demuxer.next(&mut session) => {
                match item?.ok_or_else(|| anyhow!("EOF"))? {
                    Item::Message(m) => {
                        info!(
                            "{}: {}\n",
                            m.timestamp,
                            String::from_utf8_lossy(&m.data),
                        );
                    },
                    _ => continue,
                };
            },
            _ = &mut stop => {
                break;
            },
        }
    }
    Ok(())
}
