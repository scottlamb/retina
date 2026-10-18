// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Helpers shared by the send-side integration tests.

#![allow(dead_code)] // not every test uses every helper.

use std::num::NonZeroU32;

use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, FrameInfo, Loss, LossReason, Payload, PayloadSink, VideoData, VideoDepacketizer,
    VideoFrameEnd, VideoFrameStart, VideoHandler, VideoPacketizer,
};
use retina::rtp::ReceivedPacketRef;
use retina::rtp::{OutgoingPacket, PacketHeader, ReceivedPacketMeta, Sender};

/// Pushes raw RTP packets into a depacketizer, computing loss from sequence
/// numbers. (No timestamp wraparound handling; the capture is short.)
pub struct Feeder {
    buf: MarkBuf,
    next_seq: Option<u16>,
}

impl Feeder {
    pub fn new() -> Self {
        Self {
            buf: MarkBuf::new(1 << 20),
            next_seq: None,
        }
    }

    pub fn push(
        &mut self,
        raw: &[u8],
        d: &mut VideoDepacketizer<()>,
        h: &mut impl VideoHandler<()>,
    ) -> PacketHeader {
        let (header, payload) = PacketHeader::validate(raw).unwrap();
        let loss = self
            .next_seq
            .map_or(0, |s| header.sequence_number().wrapping_sub(s));
        self.next_seq = Some(header.sequence_number().wrapping_add(1));
        let meta = ReceivedPacketMeta {
            ctx: (),
            timestamp: retina::Timestamp::new(
                i64::from(header.timestamp()),
                NonZeroU32::new(90_000).unwrap(),
                0,
            )
            .unwrap(),
            sequence_number: header.sequence_number(),
            ssrc: header.ssrc(),
            mark: header.mark(),
            continuity: retina::rtp::Continuity::from_loss(loss),
        };
        let pos = self.buf.end();
        self.buf.extend(raw);
        self.buf.advance_unparsed(self.buf.end());
        d.push(
            &ReceivedPacketRef::new(
                meta,
                &self.buf,
                pos + u64::from(payload.start),
                payload.end - payload.start,
            ),
            h,
        );
        header
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Frame {
    pub rtp_timestamp: u32,
    pub is_random_access_point: bool,
    pub nals: Vec<Vec<u8>>,
}

/// Collects complete frames as NAL units, from streamed `data` events.
#[derive(Default)]
pub struct Collector {
    pub frames: Vec<Frame>,
    pub losses: usize,
    pub corrupt: usize,

    /// True if the last of `frames` has started but not ended.
    in_frame: bool,
}

impl VideoHandler<()> for Collector {
    fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, ()>) -> Accumulate {
        self.frames.push(Frame {
            rtp_timestamp: fs.timestamp().timestamp() as u32,
            is_random_access_point: fs.is_random_access_point(),
            nals: Vec::new(),
        });
        self.in_frame = true;
        Accumulate::No
    }

    fn data(&mut self, data: &VideoData<'_>) {
        let nals = &mut self.frames.last_mut().unwrap().nals;
        if data.position.is_first() {
            nals.push(Vec::new());
        }
        let nal = nals.last_mut().unwrap();
        for d in data.data {
            nal.extend_from_slice(d);
        }
    }

    fn frame_end(&mut self, _: &mut VideoFrameEnd<'_, ()>) {
        self.in_frame = false;
    }

    fn loss(&mut self, loss: &Loss<'_, ()>) {
        if std::mem::take(&mut self.in_frame) {
            self.frames.pop(); // abandoned.
        }
        self.losses += 1;
        if matches!(loss.reason(), LossReason::Corrupt { .. }) {
            self.corrupt += 1;
        }
    }
}

/// Builds a raw RTP packet.
pub fn rtp(seq: u16, ts: u32, mark: bool, payload: &[u8]) -> Vec<u8> {
    let mut pkt = vec![0x80, if mark { 0x80 | 96 } else { 96 }];
    pkt.extend_from_slice(&seq.to_be_bytes());
    pkt.extend_from_slice(&ts.to_be_bytes());
    pkt.extend_from_slice(&[0, 0, 0, 1]);
    pkt.extend_from_slice(payload);
    pkt
}

/// Repacketizes a depacketizer's output, as in the example on
/// [`VideoPacketizer`].
pub struct Repacketize<'a, S> {
    pub packetizer: &'a mut VideoPacketizer,
    pub sink: S,
}

impl<Ctx, S: PayloadSink> VideoHandler<Ctx> for Repacketize<'_, S> {
    fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, Ctx>) -> Accumulate {
        if let Some(p) = fs.parameters() {
            self.packetizer.set_parameters(p).unwrap();
        }
        self.packetizer
            .start_frame(FrameInfo::from(&*fs), &mut self.sink);
        Accumulate::No
    }

    fn data(&mut self, data: &VideoData<'_>) {
        self.packetizer
            .push_unit(data.position, data.data, &mut self.sink);
    }

    fn frame_end(&mut self, _: &mut VideoFrameEnd<'_, Ctx>) {
        self.packetizer.end_frame(&mut self.sink);
    }

    fn loss(&mut self, _: &Loss<'_, Ctx>) {
        self.packetizer.discontinuity(&mut self.sink);
    }
}

/// An owned copy of a sent packet, with information from its payload.
#[derive(Debug)]
pub struct Pkt {
    pub raw: Vec<u8>,
    pub sequence_number: u16,
    pub frame_start: bool,
    pub random_access_point: bool,
}

impl Pkt {
    pub fn new(payload: &Payload<'_>, pkt: &OutgoingPacket<'_>) -> Self {
        Self {
            raw: pkt.to_vec(),
            sequence_number: pkt.header.sequence_number(),
            frame_start: payload.position().is_first(),
            random_access_point: payload.is_random_access_point(),
        }
    }
}

/// A sink which builds packets with a [`Sender`] and records them.
pub struct Recorder<'a> {
    pub sender: &'a mut Sender,
    pub out: &'a mut Vec<Pkt>,
}

impl<'a> Recorder<'a> {
    pub fn new(sender: &'a mut Sender, out: &'a mut Vec<Pkt>) -> Self {
        Self { sender, out }
    }
}

impl PayloadSink for Recorder<'_> {
    fn payload(&mut self, p: &Payload<'_>) {
        let pkt = self.sender.packet(p.timestamp(), p.mark(), p.data());
        self.out.push(Pkt::new(p, &pkt));
    }

    fn discontinuity(&mut self) {
        self.sender.skip();
    }
}
