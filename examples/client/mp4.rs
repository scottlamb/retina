// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Proof-of-concept `.mp4` writer.
//!
//! This writes media data (`mdat`) to a stream, buffering parameters for a
//! `moov` atom at the end. This avoids the need to buffer the media data
//! (`mdat`) first or reserved a fixed size for the `moov`, but it will slow
//! playback, particularly when serving `.mp4` files remotely.
//!
//! For a more high-quality implementation, see [Moonfire NVR](https://github.com/scottlamb/moonfire-nvr).
//! It's better tested, places the `moov` atom at the start, can do HTTP range
//! serving for arbitrary time ranges, and supports standard and fragmented
//! `.mp4` files.
//!
//! See the BMFF spec, ISO/IEC 14496-12:2015:
//! https://github.com/scottlamb/moonfire-nvr/wiki/Standards-and-specifications
//! https://standards.iso.org/ittf/PubliclyAvailableStandards/c068960_ISO_IEC_14496-12_2015.zip

use anyhow::{anyhow, bail, Context, Error};
use bytes::{Buf, BufMut, BytesMut};
use futures::{Future, StreamExt};
use log::{debug, info, warn};
use retina::{
    client::{SetupOptions, Transport},
    codec::{AudioParameters, CodecItem, ParametersRef, VideoParameters},
};

use std::num::NonZeroU32;
use std::path::PathBuf;
use std::{convert::TryFrom, pin::Pin};
use std::{io::SeekFrom, sync::Arc};
use tokio::{
    fs::File,
    io::{AsyncSeek, AsyncSeekExt, AsyncWrite, AsyncWriteExt},
};

#[derive(structopt::StructOpt)]
pub struct Opts {
    #[structopt(flatten)]
    src: super::Source,

    /// Policy for handling the `rtptime` parameter normally seem in the `RTP-Info` header.
    /// One of `default`, `require`, `ignore`, `permissive`.
    #[structopt(default_value, long)]
    initial_timestamp: retina::client::InitialTimestampPolicy,

    /// Don't attempt to include video streams.
    #[structopt(long)]
    no_video: bool,

    /// Don't attempt to include audio streams.
    #[structopt(long)]
    no_audio: bool,

    /// Allow lost packets mid-stream without aborting.
    #[structopt(long)]
    allow_loss: bool,

    /// When to issue a `TEARDOWN` request: `auto`, `always`, or `never`.
    #[structopt(default_value, long)]
    teardown: retina::client::TeardownPolicy,

    /// Duration after which to exit automatically, in seconds.
    #[structopt(long, name = "secs")]
    duration: Option<u64>,

    /// The transport to use: `tcp` or `udp` (experimental).
    ///
    /// Note: `--allow-loss` is strongly recommended with `udp`.
    #[structopt(default_value, long)]
    transport: retina::client::Transport,

    /// Path to `.mp4` file to write.
    #[structopt(parse(try_from_str))]
    out: PathBuf,
}

/// Writes a box length for everything appended in the supplied scope.
macro_rules! write_box {
    ($buf:expr, $fourcc:expr, $b:block) => {{
        let _: &mut BytesMut = $buf; // type-check.
        let pos_start = $buf.len();
        let fourcc: &[u8; 4] = $fourcc;
        $buf.extend_from_slice(&[0, 0, 0, 0, fourcc[0], fourcc[1], fourcc[2], fourcc[3]]);
        let r = {
            $b;
        };
        let pos_end = $buf.len();
        let len = pos_end.checked_sub(pos_start).unwrap();
        $buf[pos_start..pos_start + 4].copy_from_slice(&u32::try_from(len)?.to_be_bytes()[..]);
        r
    }};
}

/// Writes `.mp4` data to a sink.
/// See module-level documentation for details.
pub struct Mp4Writer<W: AsyncWrite + AsyncSeek + Send + Unpin> {
    mdat_start: u32,
    mdat_pos: u32,
    video_params: Vec<VideoParameters>,

    /// The most recently used 1-based index within `video_params`.
    cur_video_params_sample_description_index: Option<u32>,
    audio_params: Option<Box<AudioParameters>>,
    allow_loss: bool,

    /// The (1-indexed) video sample (frame) number of each sync sample (random access point).
    video_sync_sample_nums: Vec<u32>,

    video_trak: TrakTracker,
    audio_trak: TrakTracker,
    inner: W,
}

/// A chunk: a group of samples that have consecutive byte positions and same sample description.
struct Chunk {
    first_sample_number: u32, // 1-based index
    byte_pos: u32,            // starting byte of first sample
    sample_description_index: u32,
}

/// Tracks the parts of a `trak` atom which are common between video and audio samples.
#[derive(Default)]
struct TrakTracker {
    samples: u32,
    next_pos: Option<u32>,
    chunks: Vec<Chunk>,
    sizes: Vec<u32>,

    /// The durations of samples in a run-length encoding form: (number of samples, duration).
    /// This lags one sample behind calls to `add_sample` because each sample's duration
    /// is calculated using the PTS of the following sample.
    durations: Vec<(u32, u32)>,
    last_pts: Option<i64>,
    tot_duration: u64,
}

impl TrakTracker {
    fn add_sample(
        &mut self,
        sample_description_index: u32,
        byte_pos: u32,
        size: u32,
        timestamp: retina::Timestamp,
        loss: u16,
        allow_loss: bool,
    ) -> Result<(), Error> {
        if self.samples > 0 && loss > 0 && !allow_loss {
            bail!("Lost {} RTP packets mid-stream", loss);
        }
        self.samples += 1;
        if self.next_pos != Some(byte_pos)
            || self.chunks.last().map(|c| c.sample_description_index)
                != Some(sample_description_index)
        {
            self.chunks.push(Chunk {
                first_sample_number: self.samples,
                byte_pos,
                sample_description_index,
            });
        }
        self.sizes.push(size);
        self.next_pos = Some(byte_pos + size);
        if let Some(last_pts) = self.last_pts.replace(timestamp.timestamp()) {
            let duration = timestamp.timestamp().checked_sub(last_pts).unwrap();
            self.tot_duration += u64::try_from(duration).unwrap();
            let duration = u32::try_from(duration)?;
            match self.durations.last_mut() {
                Some((s, d)) if *d == duration => *s += 1,
                _ => self.durations.push((1, duration)),
            }
        }
        Ok(())
    }

    fn finish(&mut self) {
        if self.last_pts.is_some() {
            self.durations.push((1, 0));
        }
    }

    /// Estimates the sum of the variable-sized portions of the data.
    fn size_estimate(&self) -> usize {
        (self.durations.len() * 8) + // stts
        (self.chunks.len() * 12) +   // stsc
        (self.sizes.len() * 4) +     // stsz
        (self.chunks.len() * 4) // stco
    }

    fn write_common_stbl_parts(&self, buf: &mut BytesMut) -> Result<(), Error> {
        // TODO: add an edit list so the video and audio tracks are in sync.
        write_box!(buf, b"stts", {
            buf.put_u32(0);
            buf.put_u32(u32::try_from(self.durations.len())?);
            for (samples, duration) in &self.durations {
                buf.put_u32(*samples);
                buf.put_u32(*duration);
            }
        });
        write_box!(buf, b"stsc", {
            buf.put_u32(0); // version
            buf.put_u32(u32::try_from(self.chunks.len())?);
            let mut prev_sample_number = 1;
            let mut chunk_number = 1;
            if !self.chunks.is_empty() {
                for c in &self.chunks[1..] {
                    buf.put_u32(chunk_number);
                    buf.put_u32(c.first_sample_number - prev_sample_number);
                    buf.put_u32(c.sample_description_index);
                    prev_sample_number = c.first_sample_number;
                    chunk_number += 1;
                }
                buf.put_u32(chunk_number);
                buf.put_u32(self.samples + 1 - prev_sample_number);
                buf.put_u32(1); // sample_description_index
            }
        });
        write_box!(buf, b"stsz", {
            buf.put_u32(0); // version
            buf.put_u32(0); // sample_size
            buf.put_u32(u32::try_from(self.sizes.len())?);
            for s in &self.sizes {
                buf.put_u32(*s);
            }
        });
        write_box!(buf, b"stco", {
            buf.put_u32(0); // version
            buf.put_u32(u32::try_from(self.chunks.len())?); // entry_count
            for c in &self.chunks {
                buf.put_u32(c.byte_pos);
            }
        });
        Ok(())
    }
}

impl<W: AsyncWrite + AsyncSeek + Send + Unpin> Mp4Writer<W> {
    pub async fn new(
        audio_params: Option<Box<AudioParameters>>,
        allow_loss: bool,
        mut inner: W,
    ) -> Result<Self, Error> {
        let mut buf = BytesMut::new();
        write_box!(&mut buf, b"ftyp", {
            buf.extend_from_slice(&[
                b'i', b's', b'o', b'm', // major_brand
                0, 0, 0, 0, // minor_version
                b'i', b's', b'o', b'm', // compatible_brands[0]
            ]);
        });
        buf.extend_from_slice(&b"\0\0\0\0mdat"[..]);
        let mdat_start = u32::try_from(buf.len())?;
        inner.write_all(&buf).await?;
        Ok(Mp4Writer {
            inner,
            video_params: Vec::new(),
            cur_video_params_sample_description_index: None,
            audio_params,
            allow_loss,
            video_trak: TrakTracker::default(),
            audio_trak: TrakTracker::default(),
            video_sync_sample_nums: Vec::new(),
            mdat_start,
            mdat_pos: mdat_start,
        })
    }

    pub async fn finish(mut self) -> Result<(), Error> {
        self.video_trak.finish();
        self.audio_trak.finish();
        let mut buf = BytesMut::with_capacity(
            1024 + self.video_trak.size_estimate()
                + self.audio_trak.size_estimate()
                + 4 * self.video_sync_sample_nums.len(),
        );
        write_box!(&mut buf, b"moov", {
            write_box!(&mut buf, b"mvhd", {
                buf.put_u32(1 << 24); // version
                buf.put_u64(0); // creation_time
                buf.put_u64(0); // modification_time
                buf.put_u32(90000); // timescale
                buf.put_u64(self.video_trak.tot_duration);
                buf.put_u32(0x00010000); // rate
                buf.put_u16(0x0100); // volume
                buf.put_u16(0); // reserved
                buf.put_u64(0); // reserved
                for v in &[0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000] {
                    buf.put_u32(*v); // matrix
                }
                for _ in 0..6 {
                    buf.put_u32(0); // pre_defined
                }
                buf.put_u32(2); // next_track_id
            });
            if self.video_trak.samples > 0 {
                self.write_video_trak(&mut buf)?;
            }
            if self.audio_trak.samples > 0 {
                self.write_audio_trak(&mut buf, self.audio_params.as_ref().unwrap())?;
            }
        });
        self.inner.write_all(&buf).await?;
        self.inner
            .seek(SeekFrom::Start(u64::from(self.mdat_start - 8)))
            .await?;
        self.inner
            .write_all(&u32::try_from(self.mdat_pos + 8 - self.mdat_start)?.to_be_bytes()[..])
            .await?;
        Ok(())
    }

    fn write_video_trak(&self, buf: &mut BytesMut) -> Result<(), Error> {
        write_box!(buf, b"trak", {
            write_box!(buf, b"tkhd", {
                buf.put_u32((1 << 24) | 7); // version, flags
                buf.put_u64(0); // creation_time
                buf.put_u64(0); // modification_time
                buf.put_u32(1); // track_id
                buf.put_u32(0); // reserved
                buf.put_u64(self.video_trak.tot_duration);
                buf.put_u64(0); // reserved
                buf.put_u16(0); // layer
                buf.put_u16(0); // alternate_group
                buf.put_u16(0); // volume
                buf.put_u16(0); // reserved
                for v in &[0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000] {
                    buf.put_u32(*v); // matrix
                }
                let dims = self.video_params.iter().fold((0, 0), |prev_dims, p| {
                    let dims = p.pixel_dimensions();
                    (
                        std::cmp::max(prev_dims.0, dims.0),
                        std::cmp::max(prev_dims.1, dims.1),
                    )
                });
                let width = u32::from(u16::try_from(dims.0)?) << 16;
                let height = u32::from(u16::try_from(dims.1)?) << 16;
                buf.put_u32(width);
                buf.put_u32(height);
            });
            write_box!(buf, b"mdia", {
                write_box!(buf, b"mdhd", {
                    buf.put_u32(1 << 24); // version
                    buf.put_u64(0); // creation_time
                    buf.put_u64(0); // modification_time
                    buf.put_u32(90000); // timebase
                    buf.put_u64(self.video_trak.tot_duration);
                    buf.put_u32(0x55c40000); // language=und + pre-defined
                });
                write_box!(buf, b"hdlr", {
                    buf.extend_from_slice(&[
                        0x00, 0x00, 0x00, 0x00, // version + flags
                        0x00, 0x00, 0x00, 0x00, // pre_defined
                        b'v', b'i', b'd', b'e', // handler = vide
                        0x00, 0x00, 0x00, 0x00, // reserved[0]
                        0x00, 0x00, 0x00, 0x00, // reserved[1]
                        0x00, 0x00, 0x00, 0x00, // reserved[2]
                        0x00, // name, zero-terminated (empty)
                    ]);
                });
                write_box!(buf, b"minf", {
                    write_box!(buf, b"vmhd", {
                        buf.put_u32(1);
                        buf.put_u64(0);
                    });
                    write_box!(buf, b"dinf", {
                        write_box!(buf, b"dref", {
                            buf.put_u32(0);
                            buf.put_u32(1); // entry_count
                            write_box!(buf, b"url ", {
                                buf.put_u32(1); // version, flags=self-contained
                            });
                        });
                    });
                    write_box!(buf, b"stbl", {
                        write_box!(buf, b"stsd", {
                            buf.put_u32(0); // version
                            buf.put_u32(u32::try_from(self.video_params.len())?); // entry_count
                            for p in &self.video_params {
                                self.write_video_sample_entry(buf, p)?;
                            }
                        });
                        self.video_trak.write_common_stbl_parts(buf)?;
                        write_box!(buf, b"stss", {
                            buf.put_u32(0); // version
                            buf.put_u32(u32::try_from(self.video_sync_sample_nums.len())?);
                            for n in &self.video_sync_sample_nums {
                                buf.put_u32(*n);
                            }
                        });
                    });
                });
            });
        });
        Ok(())
    }

    fn write_audio_trak(
        &self,
        buf: &mut BytesMut,
        parameters: &AudioParameters,
    ) -> Result<(), Error> {
        write_box!(buf, b"trak", {
            write_box!(buf, b"tkhd", {
                buf.put_u32((1 << 24) | 7); // version, flags
                buf.put_u64(0); // creation_time
                buf.put_u64(0); // modification_time
                buf.put_u32(2); // track_id
                buf.put_u32(0); // reserved
                buf.put_u64(self.audio_trak.tot_duration);
                buf.put_u64(0); // reserved
                buf.put_u16(0); // layer
                buf.put_u16(0); // alternate_group
                buf.put_u16(0); // volume
                buf.put_u16(0); // reserved
                for v in &[0x00010000, 0, 0, 0, 0x00010000, 0, 0, 0, 0x40000000] {
                    buf.put_u32(*v); // matrix
                }
                buf.put_u32(0); // width
                buf.put_u32(0); // height
            });
            write_box!(buf, b"mdia", {
                write_box!(buf, b"mdhd", {
                    buf.put_u32(1 << 24); // version
                    buf.put_u64(0); // creation_time
                    buf.put_u64(0); // modification_time
                    buf.put_u32(parameters.clock_rate());
                    buf.put_u64(self.audio_trak.tot_duration);
                    buf.put_u32(0x55c40000); // language=und + pre-defined
                });
                write_box!(buf, b"hdlr", {
                    buf.extend_from_slice(&[
                        0x00, 0x00, 0x00, 0x00, // version + flags
                        0x00, 0x00, 0x00, 0x00, // pre_defined
                        b's', b'o', b'u', b'n', // handler = soun
                        0x00, 0x00, 0x00, 0x00, // reserved[0]
                        0x00, 0x00, 0x00, 0x00, // reserved[1]
                        0x00, 0x00, 0x00, 0x00, // reserved[2]
                        0x00, // name, zero-terminated (empty)
                    ]);
                });
                write_box!(buf, b"minf", {
                    write_box!(buf, b"smhd", {
                        buf.extend_from_slice(&[
                            0x00, 0x00, 0x00, 0x00, // version + flags
                            0x00, 0x00, // balance
                            0x00, 0x00, // reserved
                        ]);
                    });
                    write_box!(buf, b"dinf", {
                        write_box!(buf, b"dref", {
                            buf.put_u32(0);
                            buf.put_u32(1); // entry_count
                            write_box!(buf, b"url ", {
                                buf.put_u32(1); // version, flags=self-contained
                            });
                        });
                    });
                    write_box!(buf, b"stbl", {
                        write_box!(buf, b"stsd", {
                            buf.put_u32(0); // version
                            buf.put_u32(1); // entry_count
                            buf.extend_from_slice(
                                &parameters
                                    .sample_entry()
                                    .expect("all added streams have sample entries")[..],
                            );
                        });
                        self.audio_trak.write_common_stbl_parts(buf)?;

                        // AAC requires two samples (really, each is a set of 960 or 1024 samples)
                        // to decode accurately. See
                        // https://developer.apple.com/library/archive/documentation/QuickTime/QTFF/QTFFAppenG/QTFFAppenG.html .
                        write_box!(buf, b"sgpd", {
                            // BMFF section 8.9.3: SampleGroupDescriptionBox
                            buf.put_u32(0); // version
                            buf.extend_from_slice(b"roll"); // grouping type
                            buf.put_u32(1); // entry_count
                                            // BMFF section 10.1: AudioRollRecoveryEntry
                            buf.put_i16(-1); // roll_distance
                        });
                        write_box!(buf, b"sbgp", {
                            // BMFF section 8.9.2: SampleToGroupBox
                            buf.put_u32(0); // version
                            buf.extend_from_slice(b"roll"); // grouping type
                            buf.put_u32(1); // entry_count
                            buf.put_u32(self.audio_trak.samples);
                            buf.put_u32(1); // group_description_index
                        });
                    });
                });
            });
        });
        Ok(())
    }

    fn write_video_sample_entry(
        &self,
        buf: &mut BytesMut,
        parameters: &VideoParameters,
    ) -> Result<(), Error> {
        // TODO: this should move to client::VideoParameters::sample_entry() or some such.
        write_box!(buf, b"avc1", {
            buf.put_u32(0);
            buf.put_u32(1); // data_reference_index = 1
            buf.extend_from_slice(&[0; 16]);
            buf.put_u16(u16::try_from(parameters.pixel_dimensions().0)?);
            buf.put_u16(u16::try_from(parameters.pixel_dimensions().1)?);
            buf.extend_from_slice(&[
                0x00, 0x48, 0x00, 0x00, // horizresolution
                0x00, 0x48, 0x00, 0x00, // vertresolution
                0x00, 0x00, 0x00, 0x00, // reserved
                0x00, 0x01, // frame count
                0x00, 0x00, 0x00, 0x00, // compressorname
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x00, 0x00, 0x00, //
                0x00, 0x18, 0xff, 0xff, // depth + pre_defined
            ]);
            write_box!(buf, b"avcC", {
                buf.extend_from_slice(parameters.extra_data());
            });
        });
        Ok(())
    }

    async fn video(
        &mut self,
        stream: &retina::client::Stream,
        frame: retina::codec::VideoFrame,
    ) -> Result<(), Error> {
        println!(
            "{}: {}-byte video frame",
            &frame.timestamp(),
            frame.data().remaining(),
        );
        let sample_description_index = if let (Some(i), false) = (
            self.cur_video_params_sample_description_index,
            frame.has_new_parameters(),
        ) {
            // Use the most recent sample description index for most frames, without having to
            // scan through self.video_sample_index.
            i
        } else {
            match stream.parameters() {
                Some(ParametersRef::Video(params)) => {
                    log::info!("new video params: {:?}", params);
                    let pos = self.video_params.iter().position(|p| p == params);
                    if let Some(pos) = pos {
                        u32::try_from(pos + 1)?
                    } else {
                        self.video_params.push(params.clone());
                        u32::try_from(self.video_params.len())?
                    }
                }
                None => {
                    debug!("Discarding video frame received before parameters");
                    return Ok(());
                }
                _ => unreachable!(),
            }
        };
        self.cur_video_params_sample_description_index = Some(sample_description_index);
        let size = u32::try_from(frame.data().remaining())?;
        self.video_trak.add_sample(
            sample_description_index,
            self.mdat_pos,
            size,
            frame.timestamp(),
            frame.loss(),
            self.allow_loss,
        )?;
        self.mdat_pos = self
            .mdat_pos
            .checked_add(size)
            .ok_or_else(|| anyhow!("mdat_pos overflow"))?;
        if frame.is_random_access_point() {
            self.video_sync_sample_nums
                .push(u32::try_from(self.video_trak.samples)?);
        }
        self.inner.write_all(frame.data()).await?;
        Ok(())
    }

    async fn audio(&mut self, frame: retina::codec::AudioFrame) -> Result<(), Error> {
        println!(
            "{}: {}-byte audio frame",
            frame.timestamp(),
            frame.data().remaining()
        );
        let size = u32::try_from(frame.data().remaining())?;
        self.audio_trak.add_sample(
            /* sample_description_index */ 1,
            self.mdat_pos,
            size,
            frame.timestamp(),
            frame.loss(),
            self.allow_loss,
        )?;
        self.mdat_pos = self
            .mdat_pos
            .checked_add(size)
            .ok_or_else(|| anyhow!("mdat_pos overflow"))?;
        self.inner.write_all(frame.data()).await?;
        Ok(())
    }
}

/// Copies packets from `session` to `mp4` without handling any cleanup on error.
async fn copy<'a>(
    opts: &'a Opts,
    session: &'a mut retina::client::Demuxed,
    stop_signal: Pin<Box<dyn Future<Output = Result<(), std::io::Error>>>>,
    mp4: &'a mut Mp4Writer<File>,
) -> Result<(), Error> {
    let sleep = match opts.duration {
        Some(secs) => {
            futures::future::Either::Left(tokio::time::sleep(std::time::Duration::from_secs(secs)))
        }
        None => futures::future::Either::Right(futures::future::pending()),
    };
    tokio::pin!(stop_signal);
    tokio::pin!(sleep);
    loop {
        tokio::select! {
            pkt = session.next() => {
                match pkt.ok_or_else(|| anyhow!("EOF"))?? {
                    CodecItem::VideoFrame(f) => {
                        let stream = &session.streams()[f.stream_id()];
                        let start_ctx = *f.start_ctx();
                        mp4.video(stream, f).await.with_context(
                            || format!("Error processing video frame starting with {}", start_ctx))?;
                    },
                    CodecItem::AudioFrame(f) => {
                        let ctx = *f.ctx();
                        mp4.audio(f).await.with_context(
                            || format!("Error processing audio frame, {}", ctx))?;
                    },
                    CodecItem::Rtcp(rtcp) => {
                        if let (Some(t), Some(Ok(Some(sr)))) = (rtcp.rtp_timestamp(), rtcp.pkts().next().map(retina::rtcp::PacketRef::as_sender_report)) {
                            println!("{}: SR ts={}", t, sr.ntp_timestamp());
                        }
                    },
                    _ => continue,
                };
            },
            _ = &mut stop_signal => {
                info!("Stopping due to signal");
                break;
            },
            _ = &mut sleep => {
                info!("Stopping after {} seconds", opts.duration.unwrap());
                break;
            },
        }
    }
    Ok(())
}

/// Writes the `.mp4`, including trying to finish or clean up the file.
async fn write_mp4<'a>(
    opts: &'a Opts,
    session: retina::client::Session<retina::client::Described>,
    audio_params: Option<Box<AudioParameters>>,
    stop_signal: Pin<Box<dyn Future<Output = Result<(), std::io::Error>>>>,
) -> Result<(), Error> {
    let mut session = session
        .play(
            retina::client::PlayOptions::default()
                .initial_timestamp(opts.initial_timestamp)
                .enforce_timestamps_with_max_jump_secs(NonZeroU32::new(10).unwrap()),
        )
        .await?
        .demuxed()?;

    // Append into a filename suffixed with ".partial", then try to either rename it into
    // place if it's complete or delete it otherwise.
    const PARTIAL_SUFFIX: &str = ".partial";
    let mut tmp_filename = opts.out.as_os_str().to_owned();
    tmp_filename.push(PARTIAL_SUFFIX); // OsString::push doesn't put in a '/', unlike PathBuf::.
    let tmp_filename: PathBuf = tmp_filename.into();
    let out = tokio::fs::File::create(&tmp_filename).await?;
    let mut mp4 = Mp4Writer::new(audio_params, opts.allow_loss, out).await?;
    let result = copy(opts, &mut session, stop_signal, &mut mp4).await;
    if let Err(e) = result {
        // Log errors about finishing, returning the original error.
        if let Err(e) = mp4.finish().await {
            log::error!(".mp4 finish failed: {}", e);
            if let Err(e) = tokio::fs::remove_file(&tmp_filename).await {
                log::error!("and removing .mp4 failed too: {}", e);
            }
        } else {
            if let Err(e) = tokio::fs::rename(&tmp_filename, &opts.out).await {
                log::error!("unable to move completed .mp4 into place: {}", e);
            }
        }
        Err(e)
    } else {
        // Directly return errors about finishing.
        if let Err(e) = mp4.finish().await {
            log::error!(".mp4 finish failed: {}", e);
            if let Err(e) = tokio::fs::remove_file(&tmp_filename).await {
                log::error!("and removing .mp4 failed too: {}", e);
            }
            Err(e)
        } else {
            tokio::fs::rename(&tmp_filename, &opts.out).await?;
            Ok(())
        }
    }
}

pub async fn run(opts: Opts) -> Result<(), Error> {
    if matches!(opts.transport, Transport::Udp(_)) && !opts.allow_loss {
        warn!("Using --transport=udp without strongly recommended --allow-loss!");
    }

    let creds = super::creds(opts.src.username.clone(), opts.src.password.clone());
    let stop_signal = Box::pin(tokio::signal::ctrl_c());
    let session_group = Arc::new(retina::client::SessionGroup::default());
    let mut session = retina::client::Session::describe(
        opts.src.url.clone(),
        retina::client::SessionOptions::default()
            .creds(creds)
            .session_group(session_group.clone())
            .user_agent("Retina mp4 example".to_owned())
            .teardown(opts.teardown),
    )
    .await?;
    let video_stream_i = if !opts.no_video {
        let s = session.streams().iter().position(|s| {
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
        });
        if s.is_none() {
            log::info!("No suitable video stream found");
        }
        s
    } else {
        log::info!("Ignoring video streams (if any) because of --no-video");
        None
    };
    if let Some(i) = video_stream_i {
        session
            .setup(i, SetupOptions::default().transport(opts.transport.clone()))
            .await?;
    }
    let audio_stream = if !opts.no_audio {
        let s = session
            .streams()
            .iter()
            .enumerate()
            .find_map(|(i, s)| match s.parameters() {
                // Only consider audio streams that can produce a .mp4 sample
                // entry.
                Some(retina::codec::ParametersRef::Audio(a)) if a.sample_entry().is_some() => {
                    log::info!("Using {} audio stream (rfc 6381 codec {})", s.encoding_name(), a.rfc6381_codec().unwrap());
                    Some((i, Box::new(a.clone())))
                }
                _ if s.media() == "audio" => {
                    log::info!("Ignoring {} audio stream because it can't be placed into a .mp4 file without transcoding", s.encoding_name());
                    None
                }
                _ => None,
            });
        if s.is_none() {
            log::info!("No suitable audio stream found");
        }
        s
    } else {
        log::info!("Ignoring audio streams (if any) because of --no-audio");
        None
    };
    if let Some((i, _)) = audio_stream {
        session
            .setup(i, SetupOptions::default().transport(opts.transport.clone()))
            .await?;
    }
    if video_stream_i.is_none() && audio_stream.is_none() {
        bail!("Exiting because no video or audio stream was selected; see info log messages above");
    }
    let result = write_mp4(&opts, session, audio_stream.map(|(_i, p)| p), stop_signal).await;

    // Session has now been dropped, on success or failure. A TEARDOWN should
    // be pending if necessary. session_group.await_teardown() will wait for it.
    if let Err(e) = session_group.await_teardown().await {
        log::error!("TEARDOWN failed: {}", e);
    }
    result
}
