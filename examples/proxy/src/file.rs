// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A non-RTP source: an H.264 Annex B elementary stream file, played in a
//! loop at a fixed frame rate.
//!
//! This stands in for sources such as proprietary camera protocols, which
//! supply whole frames rather than RTP packets. E.g., to make a file:
//!
//! ```text
//! ffmpeg -f lavfi -i testsrc=size=640x480:rate=30 -t 10 \
//!     -c:v libx264 -bf 0 -g 60 test.h264
//! ```

use std::num::NonZeroU32;
use std::time::Duration;

use anyhow::{Error, bail};
use retina::codec::{FrameInfo, VideoParameters};

use crate::fanout::UpstreamTrack;

/// An access unit within the file.
pub struct AccessUnit {
    /// The Annex B data, from the first NAL's start code through the last NAL.
    range: std::ops::Range<usize>,
    is_random_access_point: bool,
    is_disposable: bool,
}

pub struct File {
    data: Vec<u8>,
    aus: Vec<AccessUnit>,
    pub parameters: VideoParameters,
}

impl File {
    pub fn open(path: &std::path::Path) -> Result<Self, Error> {
        let data = std::fs::read(path)?;
        let (aus, parameters) = split(&data)?;
        log::info!("{}: {} frames", path.display(), aus.len());
        Ok(Self {
            data,
            aus,
            parameters,
        })
    }

    /// Plays the file in a loop forever.
    pub async fn play(self, fps: f64, mut track: UpstreamTrack) -> Result<(), Error> {
        let clock_rate = NonZeroU32::new(90_000).unwrap();
        let frame_duration = (90_000.0 / fps).round() as i64;
        let mut interval = tokio::time::interval(Duration::from_secs_f64(1.0 / fps));
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
        let mut timestamp = 0;
        loop {
            for au in &self.aus {
                interval.tick().await;
                track.push_frame(
                    FrameInfo::new(retina::Timestamp::new(timestamp, clock_rate, 0).unwrap())
                        .with_random_access_point(au.is_random_access_point)
                        .with_disposable(au.is_disposable),
                    &self.data[au.range.clone()],
                );
                timestamp += frame_duration;
            }
        }
    }
}

/// Splits Annex B data into access units, and finds the first parameters.
fn split(data: &[u8]) -> Result<(Vec<AccessUnit>, VideoParameters), Error> {
    // NAL units, as (start code position, body range).
    let mut nals = Vec::new();
    let mut i = 0;
    let mut prev: Option<(usize, usize)> = None;
    while i + 3 <= data.len() {
        if data[i..i + 3] == [0, 0, 1] {
            let sc = if i > 0 && data[i - 1] == 0 { i - 1 } else { i };
            if let Some((prev_sc, prev_body)) = prev {
                nals.push((prev_sc, prev_body..sc));
            }
            prev = Some((sc, i + 3));
            i += 3;
        } else {
            i += 1;
        }
    }
    if let Some((sc, body)) = prev {
        nals.push((sc, body..data.len()));
    }

    let mut aus: Vec<AccessUnit> = Vec::new();
    let mut sps = None;
    let mut pps = None;
    let mut cur: Option<(AccessUnit, bool)> = None; // (au, has VCL NAL)
    for (sc, body) in nals {
        let nal = &data[body.clone()];
        let Some(&hdr) = nal.first() else { continue };
        let nal_type = hdr & 0x1f;
        let is_vcl = matches!(nal_type, 1 | 5);
        match nal_type {
            7 if sps.is_none() => sps = Some(nal),
            8 if pps.is_none() => pps = Some(nal),
            _ => {}
        }

        // A new access unit starts with an AUD, SPS, PPS, or SEI after a VCL
        // NAL, or with a VCL NAL whose first_mb_in_slice is 0.
        let starts_au = match nal_type {
            6..=9 => true,
            1 | 5 => nal.get(1).is_some_and(|b| b & 0x80 != 0),
            _ => false,
        };
        if let Some((au, has_vcl)) = &mut cur {
            if *has_vcl && starts_au {
                aus.push(cur.take().unwrap().0);
            } else {
                au.range.end = body.end;
                if is_vcl {
                    *has_vcl = true;
                    au.is_random_access_point |= nal_type == 5;
                    au.is_disposable &= hdr & 0x60 == 0;
                }
                continue;
            }
        }
        cur = Some((
            AccessUnit {
                range: sc..body.end,
                is_random_access_point: nal_type == 5,
                is_disposable: !is_vcl || hdr & 0x60 == 0,
            },
            is_vcl,
        ));
    }
    if let Some((au, true)) = cur {
        aus.push(au);
    }
    if aus.is_empty() {
        bail!("no H.264 access units found");
    }
    if !aus[0].is_random_access_point {
        bail!("file must start with an IDR frame");
    }
    let (Some(sps), Some(pps)) = (sps, pps) else {
        bail!("no SPS/PPS found");
    };
    Ok((
        aus,
        retina::codec::h264::parameters_from_sps_and_pps(sps, pps)?,
    ))
}
