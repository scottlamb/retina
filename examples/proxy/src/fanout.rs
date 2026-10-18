// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Fan-out from one upstream stream to many downstreams.
//!
//! The upstream task depacketizes each stream once. Every downstream has its
//! own packetizer and [`retina::rtp::Sender`], writing straight into its
//! connection's send buffer ([`ConnOut`]), so each downstream can be throttled
//! independently.

use std::io::IoSlice;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use log::{debug, warn};
use retina::PacketContext;
use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, FrameInfo, Loss, Payload, PayloadFormat, PayloadSink, VideoData, VideoDepacketizer,
    VideoFrameEnd, VideoFrameStart, VideoHandler, VideoPacketizer, VideoParameters,
};
use retina::rtp::ReceivedPacketRef;
use retina::rtp::{OutgoingPacket, Sender};

/// Above this many unsent bytes, a connection is congested: its packetizers
/// drop frames. A few frames' worth at typical camera bitrates.
const SOFT_LIMIT: usize = 256 << 10;

/// Above this many unsent bytes, packets are dropped outright.
const HARD_LIMIT: usize = 1 << 20;

/// The send side of a downstream connection: a buffer of bytes to write,
/// shared between producers (the connection's RTSP responses, and the upstream
/// task's packets) and the connection's writer task.
///
/// Producers append whole messages under the lock, so interleaved packets and
/// RTSP responses never split each other.
pub struct ConnOut {
    inner: Mutex<ConnOutInner>,
    notify: tokio::sync::Notify,
}

struct ConnOutInner {
    /// Bytes to write. `MarkBuf`'s "unparsed" region is what hasn't been
    /// written yet; written bytes are reclaimed as more are appended.
    buf: MarkBuf,
    closed: bool,
}

impl ConnOut {
    pub fn new() -> Self {
        Self {
            inner: Mutex::new(ConnOutInner {
                buf: MarkBuf::new(64 << 10),
                closed: false,
            }),
            notify: tokio::sync::Notify::new(),
        }
    }

    /// Appends an RTSP response, regardless of limits.
    pub fn write_rtsp(&self, data: &[u8]) {
        let mut l = self.inner.lock().unwrap();
        if l.closed {
            return;
        }
        l.buf.extend(data);
        drop(l);
        self.notify.notify_one();
    }

    /// Appends an interleaved data message, unless over the hard limit.
    /// Returns false if closed.
    fn write_data(&self, channel: u8, pieces: &[&[u8]]) -> bool {
        let len: usize = pieces.iter().map(|p| p.len()).sum();
        let len = u16::try_from(len).expect("RTP packets fit in u16");
        let mut l = self.inner.lock().unwrap();
        if l.closed {
            return false;
        }
        if l.buf.unparsed_len() > HARD_LIMIT {
            debug!("dropping packet on full connection");
            return true;
        }
        let len = len.to_be_bytes();
        l.buf.extend(&[b'$', channel, len[0], len[1]]);
        for p in pieces {
            l.buf.extend(p);
        }
        drop(l);
        self.notify.notify_one();
        true
    }

    fn write_packet(&self, channel: u8, pkt: &OutgoingPacket<'_>) -> bool {
        let mut pieces = Vec::with_capacity(1 + pkt.data.len());
        pieces.push(&pkt.header.as_bytes()[..]);
        pieces.extend_from_slice(pkt.data);
        self.write_data(channel, &pieces)
    }

    fn congested(&self) -> bool {
        self.inner.lock().unwrap().buf.unparsed_len() > SOFT_LIMIT
    }

    pub fn is_closed(&self) -> bool {
        self.inner.lock().unwrap().closed
    }

    pub fn close(&self) {
        self.inner.lock().unwrap().closed = true;
        self.notify.notify_one();
    }

    /// Writes buffered bytes to `w` until closed or an error occurs.
    pub async fn write_loop(&self, w: tokio::net::tcp::OwnedWriteHalf) -> std::io::Result<()> {
        let r = self.write_loop_inner(&w).await;
        self.close();
        r
    }

    async fn write_loop_inner(&self, w: &tokio::net::tcp::OwnedWriteHalf) -> std::io::Result<()> {
        loop {
            // Wait for something to write.
            loop {
                {
                    let l = self.inner.lock().unwrap();
                    if l.closed {
                        return Ok(());
                    }
                    if l.buf.unparsed_len() > 0 {
                        break;
                    }
                }
                self.notify.notified().await;
            }
            w.writable().await?;
            let mut l = self.inner.lock().unwrap();
            let (a, b) = l.buf.unparsed_split().slices();
            match w.try_write_vectored(&[IoSlice::new(a), IoSlice::new(b)]) {
                Ok(n) => {
                    let pos = l.buf.unparsed() + n as u64;
                    l.buf.advance_unparsed(pos);
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(e) => return Err(e),
            }
        }
    }
}

/// One downstream's view of one stream.
pub struct Downstream {
    pub sender: Sender,

    /// The interleaved channel for RTP; RTCP uses the next one.
    pub channel: u8,
    pub conn: Arc<ConnOut>,

    /// Cleared when the downstream's session closes.
    pub alive: Arc<AtomicBool>,

    /// For repacketized video: the downstream's own packetizer.
    pub packetizer: Option<VideoPacketizer>,

    /// For repacketized video: true once the downstream has started at a
    /// random access point.
    pub joined: bool,
}

impl Downstream {
    fn is_alive(&self) -> bool {
        self.alive.load(Ordering::Relaxed) && !self.conn.is_closed()
    }
}

/// Delivers a downstream's packets to its connection.
struct DownstreamSink<'a> {
    sender: &'a mut Sender,
    channel: u8,
    conn: &'a ConnOut,
}

impl PayloadSink for DownstreamSink<'_> {
    fn payload(&mut self, payload: &Payload<'_>) {
        // A packet dropped over the hard limit has still consumed a sequence
        // number, so the receiver sees ordinary packet loss.
        let pkt = self
            .sender
            .packet(payload.timestamp(), payload.mark(), payload.data());
        self.conn.write_packet(self.channel, &pkt);
    }

    fn discontinuity(&mut self) {
        self.sender.skip();
    }

    fn congested(&self) -> bool {
        self.conn.congested()
    }
}

/// The format of a track, as described to downstreams in SDP.
#[derive(Clone)]
pub struct TrackFormat {
    pub format: PayloadFormat,

    /// For repacketized video: the current parameters.
    pub parameters: Option<VideoParameters>,
}

impl TrackFormat {
    pub fn video(parameters: &VideoParameters) -> Self {
        Self {
            format: parameters
                .payload_format()
                .expect("H.264 or H.265 parameters"),
            parameters: Some(parameters.clone()),
        }
    }
}

/// The upstream task's state for one stream.
pub struct UpstreamTrack {
    pub kind: UpstreamKind,
    pub downstreams: Vec<Downstream>,
    pub joins: tokio::sync::mpsc::UnboundedReceiver<Downstream>,
    pub format: tokio::sync::watch::Sender<Option<TrackFormat>>,
}

pub enum UpstreamKind {
    /// H.264, depacketized once and repacketized per downstream.
    Video(VideoDepacketizer<PacketContext>),

    /// Anything else: payloads are forwarded as-is.
    Passthrough,

    /// H.264 from a non-RTP source, supplied frame by frame via
    /// [`UpstreamTrack::push_frame`].
    Frames,
}

impl UpstreamTrack {
    /// Handles an upstream RTP packet.
    pub fn push(&mut self, pkt: &ReceivedPacketRef<'_, PacketContext>) {
        while let Ok(d) = self.joins.try_recv() {
            self.downstreams.push(d);
        }
        match &mut self.kind {
            UpstreamKind::Video(d) => d.push(
                pkt,
                &mut FanOut {
                    downstreams: &mut self.downstreams,
                    format: &self.format,
                },
            ),
            UpstreamKind::Frames => unreachable!("RTP packet for a frame-based track"),
            UpstreamKind::Passthrough => {
                self.downstreams.retain(Downstream::is_alive);
                let meta = &pkt.meta;
                let payload = pkt.payload();
                let (a, b) = payload.slices();
                let data = [a, b];
                for d in &mut self.downstreams {
                    // Skip sequence numbers so downstream sees the loss. At
                    // a discontinuity, the count is unknown; skip one.
                    let skip = match meta.continuity {
                        retina::rtp::Continuity::Lost(n) => n.get(),
                        retina::rtp::Continuity::Discontinuity => 1,
                        _ => 0,
                    };
                    for _ in 0..skip {
                        d.sender.skip();
                    }
                    if d.conn.congested() {
                        d.sender.skip();
                        continue;
                    }
                    let pkt = d.sender.packet(meta.timestamp, meta.mark, &data);
                    d.conn.write_packet(d.channel, &pkt);
                }
            }
        }
    }

    /// Handles a whole H.264 frame in Annex B format, from a non-RTP source.
    pub fn push_frame(&mut self, frame: FrameInfo, data: &[u8]) {
        while let Ok(d) = self.joins.try_recv() {
            self.downstreams.push(d);
        }
        self.downstreams.retain(Downstream::is_alive);
        for d in &mut self.downstreams {
            d.joined |= frame.is_random_access_point();
            if !d.joined {
                continue;
            }
            let r = d
                .packetizer
                .as_mut()
                .expect("video downstream has packetizer")
                .push_frame(
                    frame,
                    retina::codec::h26x::Framing::AnnexB,
                    data,
                    &mut DownstreamSink {
                        sender: &mut d.sender,
                        channel: d.channel,
                        conn: &d.conn,
                    },
                );
            if let Err(e) = r {
                warn!("unable to packetize frame: {e}");
            }
        }
    }

    /// Forwards an upstream sender report, so downstreams can map RTP
    /// timestamps to the same wall clock.
    pub fn sender_report(&mut self, ntp: retina::NtpTimestamp, timestamp: retina::Timestamp) {
        for d in &self.downstreams {
            if d.is_alive() && (d.joined || d.packetizer.is_none()) {
                let sr = d.sender.sender_report(ntp, timestamp);
                d.conn.write_data(d.channel + 1, &[&sr]);
            }
        }
    }
}

/// A [`VideoHandler`] which feeds each downstream's packetizer.
struct FanOut<'a> {
    downstreams: &'a mut Vec<Downstream>,
    format: &'a tokio::sync::watch::Sender<Option<TrackFormat>>,
}

impl FanOut<'_> {
    /// Calls `f` with the packetizer and sink of each joined downstream.
    fn each(&mut self, mut f: impl FnMut(&mut VideoPacketizer, &mut DownstreamSink<'_>)) {
        for d in self.downstreams.iter_mut().filter(|d| d.joined) {
            f(
                d.packetizer
                    .as_mut()
                    .expect("video downstream has packetizer"),
                &mut DownstreamSink {
                    sender: &mut d.sender,
                    channel: d.channel,
                    conn: &d.conn,
                },
            );
        }
    }
}

impl VideoHandler<PacketContext> for FanOut<'_> {
    fn frame_start(&mut self, fs: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        if let Some(p) = fs.parameters() {
            self.format.send_if_modified(|f| {
                if f.as_ref().and_then(|f| f.parameters.as_ref()) == Some(p) {
                    return false;
                }
                *f = Some(TrackFormat::video(p));
                true
            });
        }
        self.downstreams.retain(Downstream::is_alive);
        if fs.is_random_access_point() {
            for d in self.downstreams.iter_mut().filter(|d| !d.joined) {
                debug!("downstream joining at {}", fs.timestamp());
                d.joined = true;
            }
        }
        let frame = FrameInfo::from(&*fs);
        let parameters = fs.parameters();
        self.each(|p, sink| {
            if let Some(parameters) = parameters
                && let Err(e) = p.set_parameters(parameters)
            {
                warn!("unable to repacketize with new parameters: {e}");
            }
            p.start_frame(frame, sink);
        });
        Accumulate::No
    }

    fn data(&mut self, data: &VideoData<'_>) {
        self.each(|p, sink| p.push_unit(data.position, data.data, sink));
    }

    fn frame_end(&mut self, _frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        self.each(|p, sink| p.end_frame(sink));
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        warn!("upstream loss: {:?}", loss.reason());
        self.each(|p, sink| p.discontinuity(sink));
    }
}
