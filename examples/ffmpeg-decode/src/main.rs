// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

extern crate ffmpeg_next as ffmpeg;

use anyhow::{anyhow, bail, Error};
use futures::StreamExt;
use log::{error, info};
use retina::{
    client::SetupOptions,
    codec::{CodecItem, ParametersRef, VideoFrame, VideoParameters},
};
use std::{fs::File, io::Write, str::FromStr, sync::Arc};
use structopt::StructOpt;

/// Decodes H.264 streams using ffmpeg, writing them into `frame<i>.ppm` images.
///
/// TODO: this only appears to generate proper images with
/// `--convert-to-annex-b`. Unsure why the default AVC isn't working.
#[derive(StructOpt)]
struct Opts {
    /// `rtsp://` URL to connect to.
    #[structopt(long, parse(try_from_str))]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[structopt(long)]
    username: Option<String>,

    /// Password; requires username.
    #[structopt(long, requires = "username")]
    password: Option<String>,

    /// When to issue a `TEARDOWN` request: `auto`, `always`, or `never`.
    #[structopt(default_value, long)]
    teardown: retina::client::TeardownPolicy,

    /// The transport to use: `tcp` or `udp` (experimental).
    #[structopt(default_value, long)]
    transport: retina::client::Transport,

    #[structopt(long)]
    convert_to_annex_b: bool,
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

struct H264Processor {
    decoder: ffmpeg::codec::decoder::Video,
    scaler: Option<ffmpeg::software::scaling::Context>,
    frame_i: u64,
    convert_to_annex_b: bool,
}

impl H264Processor {
    fn new(convert_to_annex_b: bool) -> Self {
        let mut codec_opts = ffmpeg::Dictionary::new();
        if !convert_to_annex_b {
            codec_opts.set("is_avc", "1");
        }
        let codec = ffmpeg::codec::decoder::find(ffmpeg::codec::Id::H264).unwrap();
        let decoder = ffmpeg::codec::decoder::Decoder(ffmpeg::codec::Context::new())
            .open_as_with(codec, codec_opts)
            .unwrap()
            .video()
            .unwrap();
        Self {
            decoder,
            scaler: None,
            frame_i: 0,
            convert_to_annex_b,
        }
    }

    fn handle_parameters(&mut self, p: &VideoParameters) -> Result<(), Error> {
        if !self.convert_to_annex_b {
            let pkt = ffmpeg::codec::packet::Packet::borrow(p.extra_data());
            self.decoder.send_packet(&pkt)?;
        } else {
            // TODO: should convert and supply SPS/PPS, rather than relying on
            // them existing in-band within frames.
        }

        // ffmpeg doesn't appear to actually handle the parameters until the
        // first full frame, so just note that the scaler needs to be
        // (re)created.
        self.scaler = None;
        Ok(())
    }

    fn send_frame(&mut self, f: VideoFrame) -> Result<(), Error> {
        let mut data = f.into_data();
        if self.convert_to_annex_b {
            convert_h264(&mut data)?;
        }
        let pkt = ffmpeg::codec::packet::Packet::borrow(&data);
        self.decoder.send_packet(&pkt)?;
        self.receive_frames()?;
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Error> {
        self.decoder.send_eof()?;
        self.receive_frames()?;
        Ok(())
    }

    fn receive_frames(&mut self) -> Result<(), Error> {
        let mut decoded = ffmpeg::util::frame::video::Video::empty();
        loop {
            match self.decoder.receive_frame(&mut decoded) {
                Err(ffmpeg::Error::Other {
                    errno: ffmpeg::util::error::EAGAIN,
                }) => {
                    // No complete frame available.
                    break;
                }
                Err(e) => bail!(e),
                Ok(()) => {}
            }

            // This frame writing logic lifted from ffmpeg-next's examples/dump-frames.rs.
            let scaler = self.scaler.get_or_insert_with(|| {
                info!(
                    "image parameters: {:?}, {}x{}",
                    self.decoder.format(),
                    self.decoder.width(),
                    self.decoder.height()
                );
                ffmpeg::software::scaling::Context::get(
                    self.decoder.format(),
                    self.decoder.width(),
                    self.decoder.height(),
                    ffmpeg::format::Pixel::RGB24,
                    320,
                    240,
                    ffmpeg::software::scaling::Flags::BILINEAR,
                )
                .unwrap()
            });
            let mut scaled = ffmpeg::util::frame::video::Video::empty();
            scaler.run(&decoded, &mut scaled)?;
            let filename = format!("frame{}.ppm", self.frame_i);
            info!("writing {}", &filename);
            let mut file = File::create(filename)?;
            file.write_all(
                format!("P6\n{} {}\n255\n", scaled.width(), scaled.height()).as_bytes(),
            )?;
            file.write_all(decoded.data(0))?;
            self.frame_i += 1;
        }
        Ok(())
    }
}

/// Converts from AVC representation to the Annex B representation.
fn convert_h264(data: &mut [u8]) -> Result<(), Error> {
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
    Ok(())
}

async fn run() -> Result<(), Error> {
    let opts = Opts::from_args();
    ffmpeg::init().unwrap();
    ffmpeg::util::log::set_level(ffmpeg::util::log::Level::Trace);
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
    let mut session = retina::client::Session::describe(
        opts.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .session_group(upstream_session_group.clone())
            .user_agent("Retina ffmpeg-decode example".to_owned())
            .teardown(opts.teardown),
    )
    .await?;

    let video_stream_i = session
        .streams()
        .iter()
        .position(|s| {
            if s.media() == "video" {
                if s.encoding_name() == "h264" {
                    log::info!("Using h264 video stream");
                    return true;
                }
                log::info!(
                    "Ignoring {} video stream because it's unsupported",
                    s.encoding_name(),
                );
            }
            false
        })
        .ok_or_else(|| anyhow!("No h264 video stream found"))?;
    let mut processor = H264Processor::new(opts.convert_to_annex_b);
    session
        .setup(
            video_stream_i,
            SetupOptions::default().transport(opts.transport.clone()),
        )
        .await?;

    let mut session = session
        .play(retina::client::PlayOptions::default().ignore_zero_seq(true))
        .await?
        .demuxed()?;

    if let Some(ParametersRef::Video(v)) = session.streams()[video_stream_i].parameters() {
        processor.handle_parameters(v)?;
    }

    loop {
        tokio::select! {
            item = session.next() => {
                match item {
                    Some(Ok(CodecItem::VideoFrame(f))) => {
                        if f.has_new_parameters() {
                            let v = match session.streams()[video_stream_i].parameters() {
                                Some(ParametersRef::Video(v)) => v,
                                _ => unreachable!(),
                            };
                            processor.handle_parameters(v)?;
                        }
                        processor.send_frame(f)?;
                    },
                    Some(Ok(_)) => {},
                    Some(Err(e)) => {
                        return Err(anyhow!(e).context("RTSP failure"));
                    }
                    None => {
                        info!("EOF");
                        break;
                    }
                }
            },
            _ = &mut stop_signal => {
                info!("received ctrl-C");
                break;
            },
        }
    }

    processor.flush()?;
    Ok(())
}
