// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

extern crate ffmpeg_next as ffmpeg;

use anyhow::{Error, anyhow, bail};
use clap::Parser;
use futures::StreamExt;
use log::{error, info};
use retina::{
    client::SetupOptions,
    codec::{CodecItem, ParametersRef, VideoFrame, VideoParameters},
};
use std::{fs::File, io::Write, path::Path, str::FromStr, sync::Arc};

/// Decodes video streams using ffmpeg, writing them into `frame<i>.ppm` images.
#[derive(Parser)]
struct Opts {
    /// `rtsp://` URL to connect to.
    #[clap(long)]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[clap(long)]
    username: Option<String>,

    /// Password; requires username.
    #[clap(long, requires = "username")]
    password: Option<String>,

    /// When to issue a `TEARDOWN` request: `auto`, `always`, or `never`.
    #[clap(default_value_t, long)]
    teardown: retina::client::TeardownPolicy,

    /// The transport to use: `tcp` or `udp` (experimental).
    #[clap(default_value_t, long)]
    transport: retina::client::Transport,

    /// Maximum number of frames to decode before exiting. If not specified, runs forever.
    #[clap(long)]
    max_frames: Option<u64>,
}

fn init_logging() -> mylog::Handle {
    let h = mylog::Builder::new()
        .format(
            ::std::env::var("MOONFIRE_FORMAT")
                .map_err(|_| ())
                .and_then(|s| mylog::Format::from_str(&s))
                .unwrap_or(mylog::Format::Google),
        )
        .spec(::std::env::var("MOONFIRE_LOG").as_deref().unwrap_or("info"))
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

struct Processor {
    decoder: ffmpeg::codec::decoder::Video,
    scaler: Option<ffmpeg::software::scaling::Context>,
    encoded_frame_i: u64,
    decoded_frame_i: u64,
    max_frames: Option<u64>,
}

impl Processor {
    fn new(
        codec_id: ffmpeg::codec::Id,
        max_frames: Option<u64>,
        initial_parameters: Option<&VideoParameters>,
    ) -> Result<Self, Error> {
        let codec = ffmpeg::codec::decoder::find(codec_id).unwrap();
        let mut decoder = ffmpeg::codec::decoder::Decoder(ffmpeg::codec::Context::new());
        if let Some(p) = initial_parameters {
            ctx_set_extra_data(&mut decoder, p.extra_data());
        }
        let decoder = decoder.open_as(codec)?.video().unwrap();
        Ok(Self {
            decoder,
            scaler: None,
            encoded_frame_i: 0,
            decoded_frame_i: 0,
            max_frames,
        })
    }

    /// Returns Ok(false) if max_frames was reached.
    fn send_frame(
        &mut self,
        f: VideoFrame,
        new_params: Option<&VideoParameters>,
    ) -> Result<bool, Error> {
        info!("sending frame {} to ffmpeg", self.encoded_frame_i);
        let data = f.into_data();

        // XXX: It'd be better to avoid this copy, but ffmpeg-next offers only a
        // limited `packet::Borrow` (no mutable access to any aspect of the
        // packet, not just the main buffer) or a full `packet::Packet` (which
        // owns the main buffer and can be used with `add_extra_data`). This is
        // just a proof-of-concept anyway.
        let mut pkt = ffmpeg::codec::packet::Packet::copy(&data);
        if let Some(p) = new_params {
            pkt_add_extra_data(&mut pkt, p.extra_data());
        }
        self.decoder.send_packet(&pkt)?;
        self.encoded_frame_i += 1;
        self.receive_frames()
    }

    fn flush(&mut self) -> Result<(), Error> {
        self.decoder.send_eof()?;
        self.receive_frames()?;
        Ok(())
    }

    fn receive_frames(&mut self) -> Result<bool, Error> {
        let mut decoded = ffmpeg::util::frame::video::Video::empty();
        loop {
            if self.max_frames.is_some_and(|f| self.decoded_frame_i >= f) {
                return Ok(false);
            }
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

            if let Some(ref s) = self.scaler
                && (s.input().format != decoded.format()
                    || s.input().width != decoded.width()
                    || s.input().height != decoded.height())
            {
                // Image parameters changed; need to recreate scaler.
                self.scaler = None;
            }
            let scaler = self.scaler.get_or_insert_with(|| {
                info!(
                    "image parameters: {:?}, {}x{}",
                    decoded.format(),
                    decoded.width(),
                    decoded.height()
                );
                ffmpeg::software::scaling::Context::get(
                    decoded.format(),
                    decoded.width(),
                    decoded.height(),
                    ffmpeg::format::Pixel::RGB24,
                    320,
                    240,
                    ffmpeg::software::scaling::Flags::BILINEAR,
                )
                .unwrap()
            });
            let mut scaled = ffmpeg::util::frame::video::Video::empty();
            scaler.run(&decoded, &mut scaled)?;

            let filename = format!("frame{}.ppm", self.decoded_frame_i);
            info!("writing {}", &filename);
            write_ppm(&scaled, filename)?;
            self.decoded_frame_i += 1;
        }
        Ok(true)
    }
}

fn ctx_set_extra_data(ctx: &mut ffmpeg::codec::Context, extra_data: &[u8]) {
    let len_i32: i32 = extra_data.len().try_into().unwrap();
    let ffmpeg_owned = ffmpeg_owned_input_buffer(extra_data);
    unsafe {
        ffmpeg::sys::av_free((*ctx.as_mut_ptr()).extradata as *mut _);
        (*ctx.as_mut_ptr()).extradata = ffmpeg_owned;
        (*ctx.as_mut_ptr()).extradata_size = len_i32;
    }
}

fn pkt_add_extra_data(pkt: &mut ffmpeg::codec::packet::Packet, extra_data: &[u8]) {
    // TODO: add this to ffmpeg-next.
    //
    // pkt.add_side_data(
    //     ffmpeg::codec::packet::side_data::Type::NewExtraData,
    //     extra_data,
    // );
    //
    // In the meantime, do it manually:
    let ffmpeg_owned = ffmpeg_owned_input_buffer(extra_data);
    unsafe {
        use ffmpeg::packet::Mut as _;
        ffmpeg::sys::av_packet_add_side_data(
            pkt.as_mut_ptr(),
            ffmpeg::codec::packet::side_data::Type::NewExtraData.into(),
            ffmpeg_owned,
            extra_data.len(),
        );
    }
}

fn ffmpeg_owned_input_buffer(buf: &[u8]) -> *mut u8 {
    unsafe {
        let ffmpeg_owned =
            ffmpeg::sys::av_malloc(buf.len() + ffmpeg::ffi::AV_INPUT_BUFFER_PADDING_SIZE as usize)
                as *mut u8;
        assert!(!ffmpeg_owned.is_null());
        std::ptr::copy_nonoverlapping(buf.as_ptr(), ffmpeg_owned, buf.len());
        ffmpeg_owned
    }
}

// This frame writing logic lifted from ffmpeg-next's examples/dump-frames.rs and
// <https://github.com/zmwangx/rust-ffmpeg/pull/243>.
fn write_ppm(frame: &ffmpeg::util::frame::Video, filename: impl AsRef<Path>) -> Result<(), Error> {
    let mut file = std::io::BufWriter::new(File::create(filename)?);
    file.write_all(format!("P6\n{} {}\n255\n", frame.width(), frame.height()).as_bytes())?;
    for i in 0..frame.height() as usize {
        let start = i * frame.stride(0);
        let len = 3 * frame.width() as usize;
        file.write_all(&frame.data(0)[start..start + len])?;
    }
    Ok(())
}

async fn run() -> Result<(), Error> {
    let opts = Opts::parse();
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

    let (video_stream_i, ffmpeg_codec_id) = session
        .streams()
        .iter()
        .enumerate()
        .find_map(|(i, s)| {
            if s.media() == "video" {
                match s.encoding_name() {
                    "jpeg" => return Some((i, ffmpeg::codec::Id::MJPEG)),
                    "h264" => return Some((i, ffmpeg::codec::Id::H264)),
                    #[cfg(feature = "h265")]
                    "h265" => return Some((i, ffmpeg::codec::Id::H265)),
                    _ => {
                        log::info!(
                            "Ignoring {} video stream because it's unsupported",
                            s.encoding_name(),
                        );
                    }
                }
            }
            None
        })
        .ok_or_else(|| anyhow!("No supported video stream found"))?;
    session
        .setup(
            video_stream_i,
            SetupOptions::default().transport(opts.transport.clone()),
        )
        .await?;

    let mut session = session
        .play(retina::client::PlayOptions::default())
        .await?
        .demuxed()?;

    let initial_parameters = match session.streams()[video_stream_i].parameters() {
        Some(ParametersRef::Video(v)) => Some(v),
        Some(_) => unreachable!(),
        None => None,
    };
    let mut processor = Processor::new(ffmpeg_codec_id, opts.max_frames, initial_parameters)?;
    loop {
        tokio::select! {
            item = session.next() => {
                match item {
                    Some(Ok(CodecItem::VideoFrame(f))) => {
                        let params = f.has_new_parameters().then(|| match session.streams()[video_stream_i].parameters() {
                            Some(ParametersRef::Video(v)) => v,
                            _ => unreachable!(),
                        });
                        if !processor.send_frame(f, params)? {
                            break;
                        }
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
