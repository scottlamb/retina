// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Depacketizes one stream from a dump of RTSP interleaved data, without an
//! RTSP session.
//!
//! This demonstrates Retina's sans-I/O receive and depacketization APIs. The
//! input is a file of RTSP interleaved frames (`$`, a channel id, a 16-bit
//! big-endian length, and an RTP or RTCP packet), as in `benches/bunny.rtsp`.
//! The packet context is each packet's byte offset within the file. The RTP
//! channel's payload type is taken from its first packet.
//!
//! ```text
//! cargo run --features unstable-rtp-receive --example depacketize_dump -- \
//!     FILE CHANNEL MEDIA ENCODING_NAME CLOCK_RATE [FMTP]
//! ```
//!
//! For example:
//!
//! ```text
//! cargo run --features unstable-rtp-receive --example depacketize_dump -- \
//!     benches/bunny.rtsp 2 video h264 90000 \
//!     'packetization-mode=1;profile-level-id=42C01E;sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg=='
//! ```

use std::io::{IoSliceMut, Read};
use std::num::NonZeroU32;
use std::time::Instant;

use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, AudioFrameRef, AudioHandler, Depacketizer, Loss, MessageFrameRef, MessageHandler,
    PayloadFormat, VideoData, VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use retina::rtp::{PacketHeader, Received, Receiver, ReceiverOptions, ReorderOptions};

/// The packet context: the packet's byte offset within the file.
type Ctx = u64;

/// The receiver's per-packet item: the packet's offset and payload location.
struct Item {
    offset: u64,
    payload_pos: u64,
    payload_len: u16,
}

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
        // The default (raw) format can represent any frame.
        let data = frame
            .data(retina::codec::FrameFormat::default())
            .expect("raw format is infallible");
        println!(
            "audio ts={} offset={} bytes={}",
            frame.timestamp(),
            frame.ctx(),
            data.len()
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
    let clock_rate: NonZeroU32 = args[5].parse()?;
    let mut format = PayloadFormat::new(args[3].clone(), args[4].clone(), clock_rate.get());
    if let Some(fmtp) = args.get(6) {
        format = format.with_fmtp(fmtp.clone());
    }
    let mut depacketizer = Depacketizer::<Ctx>::new(&format)?;
    // The receiver is created on the channel's first RTP packet, which gives
    // the payload type. A dump has no arrival times, so there's no reordering.
    let mut receiver: Option<Receiver<Item>> = None;
    let mut handler = Printer::default();
    let now = Instant::now();
    let mut depacketize = |buf: &MarkBuf, p: Received<Item>| {
        let pkt = p.packet_ref(p.item.offset, buf, p.item.payload_pos, p.item.payload_len);
        match &mut depacketizer {
            Depacketizer::Video(d) => d.push(&pkt, &mut handler),
            Depacketizer::Audio(d) => d.push(&pkt, &mut handler),
            Depacketizer::Message(d) => d.push(&pkt, &mut handler),
            _ => {} // a media type this example doesn't know about.
        }
    };

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
            let (header, payload) = PacketHeader::validate(buf.split(pkt_pos, len.into()))
                .map_err(|e| format!("bad RTP packet at offset {offset}: {e}"))?;
            let receiver = receiver.get_or_insert_with(|| {
                let reorder = ReorderOptions::default().max_delay(std::time::Duration::ZERO);
                let options = ReceiverOptions::default().reorder(reorder);
                Receiver::new(
                    [header.payload_type()].into_iter().collect(),
                    clock_rate,
                    options,
                )
            });
            let item = Item {
                offset,
                payload_pos: pkt_pos + u64::from(payload.start),
                payload_len: payload.end - payload.start,
            };
            receiver.push(&buf, header, pkt_pos, now, item);
            while let Some(p) = receiver.pop(&buf, now) {
                depacketize(&buf, p);
            }
        }
    }

    // A lone source's first packet waits a second before it's selected.
    if let Some(receiver) = &mut receiver {
        let later = now + std::time::Duration::from_secs(1);
        while let Some(p) = receiver.pop(&buf, later) {
            depacketize(&buf, p);
        }
    }
    if buf.unparsed_len() > 0 {
        eprintln!("ignoring {} trailing bytes", buf.unparsed_len());
    }
    Ok(())
}
