// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Depacketizes one stream from a dump of RTSP interleaved data, without an
//! RTSP session.
//!
//! This demonstrates Retina's sans-I/O depacketization API. The input is a file
//! of RTSP interleaved frames (`$`, a channel id, a 16-bit big-endian length,
//! and an RTP or RTCP packet), as in `benches/bunny.rtsp`. The packet context
//! is each packet's byte offset within the file.
//!
//! ```text
//! cargo run --example depacketize_dump -- FILE CHANNEL MEDIA ENCODING_NAME CLOCK_RATE [FMTP]
//! ```
//!
//! For example:
//!
//! ```text
//! cargo run --example depacketize_dump -- benches/bunny.rtsp 2 video h264 90000 \
//!     'packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg=='
//! ```

use std::io::{IoSliceMut, Read};

use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, AudioFrameRef, AudioHandler, Depacketizer, Loss, MessageFrameRef, MessageHandler,
    PayloadFormat, VideoData, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use retina::rtp::ReceivedPacketRef;
use retina::rtp::{PacketHeader, Receiver, ReceiverOptions, ValidatedPacket};

/// The packet context: the packet's byte offset within the file.
type Ctx = u64;

/// Prints a line per frame, streaming video data rather than accumulating it.
#[derive(Default)]
struct Printer {
    units: usize,
    bytes: usize,
}

impl VideoHandler<Ctx> for Printer {
    fn frame_start(&mut self, _frame_start: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
        self.units = 0;
        self.bytes = 0;
        Accumulate::No
    }

    fn data(&mut self, data: &VideoData<'_>) {
        // A real handler might write this to a socket or decoder as it arrives.
        if data.position.is_first() {
            self.units += 1;
        }
        self.bytes += data.len();
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, Ctx>) {
        println!(
            "video ts={} offsets={}..={} rap={} disposable={} units={} bytes={}",
            frame_end.timestamp(),
            frame_end.start_ctx(),
            frame_end.end_ctx(),
            frame_end.is_random_access_point(),
            frame_end.is_disposable(),
            self.units,
            self.bytes,
        );
    }

    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        print_loss(loss);
    }
}

impl AudioHandler<Ctx> for Printer {
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        print_loss(loss);
    }

    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, Ctx>) {
        println!(
            "audio ts={} offset={} bytes={}",
            frame.timestamp(),
            frame.ctx(),
            frame.data(retina::codec::FrameFormat::default()).len()
        );
    }
}

impl MessageHandler<Ctx> for Printer {
    fn loss(&mut self, loss: &Loss<'_, Ctx>) {
        print_loss(loss);
    }

    fn message_frame(&mut self, frame: &MessageFrameRef<'_, Ctx>) {
        println!(
            "message ts={} offset={} bytes={}",
            frame.timestamp(),
            frame.ctx(),
            frame.data().len()
        );
    }
}

fn print_loss(loss: &Loss<'_, Ctx>) {
    println!("loss at offset {}: {:?}", loss.ctx(), loss.reason());
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    if !(6..=7).contains(&args.len()) {
        eprintln!(
            "usage: {} FILE CHANNEL MEDIA ENCODING_NAME CLOCK_RATE [FMTP]",
            args[0]
        );
        std::process::exit(1);
    }
    let mut file = std::fs::File::open(&args[1])?;
    let channel: u8 = args[2].parse()?;
    let clock_rate: u32 = args[5].parse()?;
    let mut format = PayloadFormat::new(args[3].clone(), args[4].clone(), clock_rate);
    if let Some(fmtp) = args.get(6) {
        format = format.with_fmtp(fmtp.clone());
    }
    let mut depacketizer = Depacketizer::<Ctx>::new(&format)?;
    let mut receiver = Receiver::new(clock_rate, ReceiverOptions::default())?;
    let mut handler = Printer::default();

    // Stream positions in `buf` count from the first byte written, so they're
    // also file offsets.
    let mut buf = MarkBuf::new(1 << 16);
    let mut eof = false;
    while !eof {
        // Read more, directly into the buffer's free space.
        let (s1, s2) = buf.spare_capacity(1 << 16);
        let n = file.read_vectored(&mut [IoSliceMut::new(s1), IoSliceMut::new(s2)])?;
        buf.advance_end(n);
        eof = n == 0;

        // Parse and depacketize each complete interleaved frame.
        while buf.unparsed_len() >= 4 {
            let hdr = buf.split(buf.unparsed(), 4).to_vec();
            if hdr[0] != b'$' {
                return Err(
                    format!("expected interleaved frame at offset {}", buf.unparsed()).into(),
                );
            }
            let len = u16::from_be_bytes([hdr[2], hdr[3]]);
            if buf.unparsed_len() < 4 + usize::from(len) {
                break; // Wait for the rest of the frame.
            }
            let offset = buf.unparsed();
            let pkt_pos = offset + 4;
            buf.advance_unparsed(pkt_pos + u64::from(len));
            if hdr[1] != channel {
                continue;
            }
            let ValidatedPacket {
                header, payload, ..
            } = PacketHeader::validate(buf.split(pkt_pos, len.into()))
                .map_err(|e| format!("bad RTP packet at offset {offset}: {e}"))?;
            let meta = receiver
                .rtp(offset, &header)
                .map_err(|e| format!("bad RTP packet at offset {offset}: {e}"))?;
            let pkt = ReceivedPacketRef::new(
                meta,
                &buf,
                pkt_pos + u64::from(payload.start),
                payload.end - payload.start,
            );
            match &mut depacketizer {
                Depacketizer::Video(d) => d.push(&pkt, &mut handler),
                Depacketizer::Audio(d) => d.push(&pkt, &mut handler),
                Depacketizer::Message(d) => d.push(&pkt, &mut handler),
                _ => {} // a media type this example doesn't know about.
            }
        }
    }
    if buf.unparsed_len() > 0 {
        eprintln!("ignoring {} trailing bytes", buf.unparsed_len());
    }
    Ok(())
}
