// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Sends a tone to a camera's speaker via the ONVIF audio backchannel.

use std::sync::Arc;
use std::time::Duration;

use anyhow::{Error, anyhow, bail};
use bytes::Bytes;
use clap::Parser;
use futures::{SinkExt as _, StreamExt as _};
use log::{error, info};
use retina::client::{PacketItem, SessionGroup, SetupOptions, StreamDirection};
use retina::rtp::SendingPacket;

/// G.711 samples per packet: 20 ms at 8 kHz, the default packetization
/// interval of RFC 3551 section 4.2 (Table 1's "ms/packet" for PCMU and PCMA).
const SAMPLES_PER_PACKET: u32 = 160;

#[derive(Parser)]
pub struct Opts {
    #[command(flatten)]
    src: super::Source,

    /// Tone frequency, in Hz.
    #[arg(long, default_value_t = 440.0)]
    frequency: f64,

    /// How long to send the tone, in seconds.
    #[arg(long, default_value_t = 5)]
    duration_secs: u64,
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
    let creds = super::creds(opts.src.username, opts.src.password);
    let mut session = retina::client::Session::describe(
        opts.src.url,
        retina::client::SessionOptions::default()
            .creds(creds)
            .user_agent("Retina backchannel example".to_owned())
            .session_group(session_group)
            .backchannel(true),
    )
    .await?;
    let mut backchannels = session
        .streams()
        .iter()
        .enumerate()
        .filter(|(_, s)| s.direction() == StreamDirection::Sending && s.media() == "audio")
        .peekable();
    if backchannels.peek().is_none() {
        bail!("server offered no audio backchannel stream");
    }
    let (stream_i, stream, encode) = backchannels
        .find_map(|(i, s)| {
            let encode: fn(i16) -> u8 = match (s.encoding_name(), s.clock_rate_hz()) {
                ("pcmu", 8_000) => linear_to_ulaw,
                ("pcma", 8_000) => linear_to_alaw,
                _ => return None,
            };
            Some((i, s, encode))
        })
        .ok_or_else(|| anyhow!("this example only sends PCMU or PCMA at 8 kHz"))?;
    info!("sending to backchannel stream {stream_i}: {stream:?}");
    session.setup(stream_i, SetupOptions::default()).await?;
    let mut session = session.play(retina::client::PlayOptions::default()).await?;

    let deadline = tokio::time::sleep(Duration::from_secs(opts.duration_secs));
    tokio::pin!(deadline);
    let mut interval = tokio::time::interval(Duration::from_millis(20));
    let mut timestamp = 0u32;
    loop {
        tokio::select! {
            _ = &mut deadline => break,
            _ = interval.tick() => {
                let payload: Bytes = (0..SAMPLES_PER_PACKET)
                    .map(|i| {
                        let t = timestamp.wrapping_add(i);
                        let phase = 2. * std::f64::consts::PI * opts.frequency * f64::from(t) / 8_000.;
                        encode((phase.sin() * f64::from(i16::MAX / 4)) as i16)
                    })
                    .collect();
                let pkt = SendingPacket::new(stream_i, timestamp, payload).mark(timestamp == 0);
                session.send(pkt).await?;
                timestamp = timestamp.wrapping_add(SAMPLES_PER_PACKET);
            },
            item = session.next() => {
                if let PacketItem::Rtcp(rtcp) = item.ok_or_else(|| anyhow!("EOF"))?? {
                    info!("RTCP from server: {rtcp:?}");
                }
            },
        }
    }
    Ok(())
}

/// Encodes a linear PCM sample as G.711 µ-law.
fn linear_to_ulaw(sample: i16) -> u8 {
    const BIAS: i32 = 0x84;
    const CLIP: i32 = 32_635;
    let s = i32::from(sample);
    let sign = if s < 0 { 0x80 } else { 0 };
    let magnitude = s.abs().min(CLIP) + BIAS;
    let exponent = 7 - ((magnitude >> 7) as u8).leading_zeros() as i32;
    let mantissa = (magnitude >> (exponent + 3)) & 0x0f;
    !((sign | (exponent << 4) | mantissa) as u8)
}

/// Encodes a linear PCM sample as G.711 A-law.
fn linear_to_alaw(sample: i16) -> u8 {
    let s = i32::from(sample) >> 3; // 13 bits.
    let (sign, magnitude) = if s >= 0 { (0x80, s) } else { (0, -s - 1) };
    let exponent = if magnitude < 32 {
        0
    } else {
        27 - (magnitude as u32).leading_zeros() as i32
    };
    let mantissa = (magnitude >> exponent.max(1)) & 0x0f;
    ((sign | (exponent << 4) | mantissa) ^ 0x55) as u8
}

#[cfg(test)]
mod tests {
    #[test]
    fn g711_silence() {
        assert_eq!(super::linear_to_ulaw(0), 0xff);
        assert_eq!(super::linear_to_alaw(0), 0xd5);
    }

    #[test]
    fn g711_extremes() {
        assert_eq!(super::linear_to_ulaw(i16::MAX), 0x80);
        assert_eq!(super::linear_to_ulaw(i16::MIN), 0x00);
        assert_eq!(super::linear_to_alaw(i16::MAX), 0xaa);
        assert_eq!(super::linear_to_alaw(i16::MIN), 0x2a);
    }
}
