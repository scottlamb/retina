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
use std::time::Instant;

use log::{debug, warn};
use retina::PacketContext;
use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, Loss, Payload, PayloadFormat, PayloadSink, VideoData, VideoDepacketizer,
    VideoFrameEnd, VideoFrameInfo, VideoFrameStart, VideoHandler, VideoPacketizer, VideoParameters,
};
use retina::rtp::{Continuity, ReceivedPacketRef};
use retina::rtp::{OutgoingPacketRef, Sender};
use retina::{NtpTimestamp, Timestamp};

/// Above this many unsent bytes, a connection is congested: its packetizers
/// drop frames. A few frames' worth at typical camera bitrates.
const SOFT_LIMIT: usize = 256 << 10;

/// Above this many unsent bytes, packets are dropped outright.
const HARD_LIMIT: usize = 1 << 20;

/// The outcome of writing a data message to a [`ConnOut`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Write {
    Written,

    /// Dropped for being over the hard limit.
    Full,

    Closed,
}

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

    /// Appends RTSP responses (in two parts), regardless of limits.
    pub fn write_rtsp(&self, (first, second): (&[u8], &[u8])) {
        let mut l = self.inner.lock().unwrap();
        if l.closed {
            return;
        }
        l.buf.extend(first);
        l.buf.extend(second);
        drop(l);
        self.notify.notify_one();
    }

    /// Stops a stream: after this returns, no more of its data (written
    /// with the same `alive`) will be appended.
    ///
    /// `alive` is cleared under the lock that writes take, so a write racing
    /// with this is either already appended (before anything appended after
    /// this returns, such as a `TEARDOWN` response) or dropped.
    pub fn stop(&self, alive: &AtomicBool) {
        let _l = self.inner.lock().unwrap();
        alive.store(false, Ordering::Relaxed);
    }

    /// Appends an interleaved data message, unless over the hard limit or
    /// the stream is stopped.
    fn write_data(&self, alive: &AtomicBool, channel: u8, pieces: &[&[u8]]) -> Write {
        let mut l = self.inner.lock().unwrap();
        let w = Self::check(&l, alive);
        if w == Write::Written {
            Self::append(&mut l, channel, pieces);
            drop(l);
            self.notify.notify_one();
        }
        w
    }

    /// Appends the RTP packet returned by `f`, unless over the hard limit or
    /// the stream is stopped.
    ///
    /// `f` is called only if the packet will be written, so a dropped packet
    /// doesn't consume a sequence number.
    fn write_packet<'a>(
        &self,
        alive: &AtomicBool,
        channel: u8,
        f: impl FnOnce() -> OutgoingPacketRef<'a>,
    ) -> Write {
        let mut l = self.inner.lock().unwrap();
        let w = Self::check(&l, alive);
        if w == Write::Written {
            let pkt = f();
            let header = pkt.header();
            let mut pieces = Vec::with_capacity(1 + pkt.data().len());
            pieces.push(&header.as_bytes()[..]);
            pieces.extend_from_slice(pkt.data());
            Self::append(&mut l, channel, &pieces);
            drop(l);
            self.notify.notify_one();
        }
        w
    }

    fn check(l: &ConnOutInner, alive: &AtomicBool) -> Write {
        if l.closed || !alive.load(Ordering::Relaxed) {
            Write::Closed
        } else if l.buf.unparsed_len() > HARD_LIMIT {
            debug!("dropping data on full connection");
            Write::Full
        } else {
            Write::Written
        }
    }

    fn append(l: &mut ConnOutInner, channel: u8, pieces: &[&[u8]]) {
        let len: usize = pieces.iter().map(|p| p.len()).sum();
        let len = u16::try_from(len).expect("RTP packets fit in u16");
        let len = len.to_be_bytes();
        l.buf.extend(&[b'$', channel, len[0], len[1]]);
        for p in pieces {
            l.buf.extend(p);
        }
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
    rtp: DownstreamRtp,

    /// For repacketized video: the downstream's own packetizer.
    packetizer: Option<VideoPacketizer>,

    /// For repacketized video: true once the downstream has started at a
    /// random access point.
    joined: bool,
}

impl Downstream {
    /// Creates a downstream which sends RTP on interleaved channel `channel`
    /// and RTCP on the next one.
    pub fn new(
        sender: Sender,
        channel: u8,
        conn: Arc<ConnOut>,
        cname: Arc<str>,
        alive: Arc<AtomicBool>,
        packetizer: Option<VideoPacketizer>,
    ) -> Self {
        Self {
            rtp: DownstreamRtp {
                sender,
                channel,
                conn,
                cname,
                alive,
                gap: false,
            },
            packetizer,
            joined: false,
        }
    }

    fn is_alive(&self) -> bool {
        self.rtp.alive.load(Ordering::Relaxed) && !self.rtp.conn.is_closed()
    }
}

/// A downstream's RTP session: where its packets go, and its state.
struct DownstreamRtp {
    sender: Sender,

    /// The interleaved channel for RTP; RTCP uses the next one.
    channel: u8,
    conn: Arc<ConnOut>,
    cname: Arc<str>,

    /// Cleared, via [`ConnOut::stop`], when the downstream's session ends.
    alive: Arc<AtomicBool>,

    /// True if data was lost since the last packet sent, so the next packet
    /// must skip a sequence number.
    ///
    /// However much was lost, one skipped sequence number suffices to show
    /// receivers the loss. Skipping more could add up, over a long congestion
    /// episode, to a jump that RFC 3550 appendix A.1 receivers take for a
    /// sender restart.
    gap: bool,
}

impl DownstreamRtp {
    /// Sends a packet, then a sender report if one is due and possible.
    fn send(
        &mut self,
        timestamp: Timestamp,
        mark: bool,
        data: &[&[u8]],
        wall_clock: Option<&WallClock>,
    ) {
        let w = self.conn.write_packet(&self.alive, self.channel, || {
            if std::mem::take(&mut self.gap) {
                self.sender.skip();
            }
            self.sender.packet(timestamp, mark, data)
        });
        match w {
            Write::Written => self.maybe_report(wall_clock),
            Write::Full => self.gap = true,
            Write::Closed => {}
        }
    }

    /// Sends a sender report if one is due.
    ///
    /// The first follows the first packet without delay; later ones follow
    /// the RFC 3550 schedule while packets flow; see [`Sender::report_due`].
    /// Reports need the source's wall clock, so there are none until it's
    /// known.
    fn maybe_report(&mut self, wall_clock: Option<&WallClock>) {
        let now = Instant::now();
        if !self.sender.report_due(now) {
            return;
        }
        let Some((ntp, timestamp)) = wall_clock.and_then(|w| w.at(now)) else {
            return;
        };
        let sr = self.sender.sender_report(ntp, timestamp, &self.cname);
        if self.conn.write_data(&self.alive, self.channel + 1, &[&sr]) == Write::Written {
            self.sender.report_sent(now);
        }
    }
}

/// The source's wall clock, as a mapping from RTP timestamps to NTP
/// timestamps, e.g. from the upstream's latest sender report.
///
/// Downstream sender reports keep the source's wall clock, rather than
/// stating when the proxy sent each packet, so downstreams learn when the
/// source captured the media.
#[derive(Copy, Clone, Debug)]
pub struct WallClock {
    pub ntp: NtpTimestamp,
    pub timestamp: Timestamp,

    /// When the mapping held, on the local monotonic clock.
    pub at: Instant,
}

impl WallClock {
    /// Returns the mapping extrapolated to `now`, as a sender report sent
    /// then should state it.
    fn at(&self, now: Instant) -> Option<(NtpTimestamp, Timestamp)> {
        let elapsed = now.saturating_duration_since(self.at).as_nanos();
        let ticks = elapsed * u128::from(self.timestamp.clock_rate().get()) / 1_000_000_000;
        let timestamp = self.timestamp.try_add(u32::try_from(ticks).ok()?)?;
        let ntp = self
            .ntp
            .0
            .wrapping_add(u64::try_from((elapsed << 32) / 1_000_000_000).ok()?);
        Some((NtpTimestamp(ntp), timestamp))
    }
}

/// Delivers a downstream's packets to its connection.
struct DownstreamSink<'a> {
    rtp: &'a mut DownstreamRtp,
    wall_clock: Option<&'a WallClock>,
}

impl PayloadSink for DownstreamSink<'_> {
    fn payload(&mut self, payload: &Payload<'_>) {
        self.rtp.send(
            payload.timestamp(),
            payload.mark(),
            payload.data(),
            self.wall_clock,
        );
    }

    fn discontinuity(&mut self) {
        self.rtp.gap = true;
    }

    fn congested(&self) -> bool {
        self.rtp.conn.congested()
    }

    fn max_payload_size(&self) -> u16 {
        self.rtp.sender.max_payload_size()
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

    /// The source's wall clock, once known.
    pub wall_clock: Option<WallClock>,
}

pub enum UpstreamKind {
    /// H.264 or H.265, depacketized once and repacketized per downstream.
    Video(VideoDepacketizer<PacketContext>),

    /// Anything else: payloads are forwarded as-is.
    Passthrough,
}

impl UpstreamTrack {
    /// Handles an upstream RTP packet.
    pub fn push(&mut self, pkt: &ReceivedPacketRef<'_, PacketContext>) {
        while let Ok(d) = self.joins.try_recv() {
            self.downstreams.push(d);
        }
        let meta = &pkt.meta;
        if meta.continuity == Continuity::Discontinuity {
            // Timestamps may not be comparable across a discontinuity, so the
            // old mapping may be wrong until the next sender report.
            self.wall_clock = None;
        }
        match &mut self.kind {
            UpstreamKind::Video(d) => {
                let mut fan_out = FanOut {
                    downstreams: &mut self.downstreams,
                    format: &self.format,
                    wall_clock: self.wall_clock.as_ref(),
                };
                d.push(pkt, &mut fan_out);

                // Don't hold the last payload until the frame's end is known,
                // which for a camera that doesn't set the marker bit is when
                // the next frame begins.
                fan_out.each(|p, sink| p.flush(sink));
            }
            UpstreamKind::Passthrough => {
                self.downstreams.retain(Downstream::is_alive);
                let payload = pkt.payload();
                let (a, b) = payload.slices();
                let data = [a, b];
                let lost = meta.continuity != Continuity::Contiguous;
                for d in &mut self.downstreams {
                    d.rtp.gap |= lost;
                    if d.rtp.conn.congested() {
                        d.rtp.gap = true;
                        continue;
                    }
                    d.rtp
                        .send(meta.timestamp, meta.mark, &data, self.wall_clock.as_ref());
                }
            }
        }
    }

    /// Notes the source's wall clock, e.g. from an upstream sender report.
    ///
    /// Each downstream sends its own sender reports, on its own schedule,
    /// extrapolating from the latest wall clock.
    pub fn set_wall_clock(&mut self, wall_clock: WallClock) {
        self.wall_clock = Some(wall_clock);
    }
}

/// A [`VideoHandler`] which feeds each downstream's packetizer.
struct FanOut<'a> {
    downstreams: &'a mut Vec<Downstream>,
    format: &'a tokio::sync::watch::Sender<Option<TrackFormat>>,
    wall_clock: Option<&'a WallClock>,
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
                    rtp: &mut d.rtp,
                    wall_clock: self.wall_clock,
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
        let frame = VideoFrameInfo::from(&*fs);
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
