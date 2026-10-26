// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::sync::Once;

static INIT_LOGGING: Once = Once::new();

// This is slightly different from `retina::testutil::init_logging()`:
// * it defaults to no logging so that fuzzing output is not polluted with log messages,
//   unless requested when drilling in.
// * it doesn't use the test writer, as fuzzing doesn't go through `libtest`.
pub fn init_logging() {
    INIT_LOGGING.call_once(|| {
        tracing_subscriber::fmt()
            .with_writer(std::io::stderr)
            .with_env_filter(
                tracing_subscriber::EnvFilter::builder()
                    .with_default_directive(tracing_subscriber::filter::LevelFilter::OFF.into())
                    .from_env_lossy(),
            )
            .init();
    })
}

use retina::buf::MarkBuf;
use retina::codec::{
    Accumulate, FrameFormat, Loss, LossReason, Position, VideoData, VideoDepacketizer,
    VideoFrameEnd, VideoFrameStart, VideoHandler,
};
use retina::rtp::ReceivedPacketRef;

/// An event recorded by [`CheckingHandler`].
#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    Frame {
        is_random_access_point: bool,
        is_disposable: bool,
        has_new_parameters: bool,

        /// The frame's units as delivered via `data`, each with a 4-byte length prefix.
        streamed: Vec<u8>,
    },
    Loss(LossReason),
}

/// A [`VideoHandler`] which checks event consistency and records events.
///
/// Uses a packet index as context, to exercise a non-`PacketContext` `Ctx`.
pub struct CheckingHandler {
    pub accumulate: Accumulate,

    /// True if `complete_frame` in `FrameFormat::MP4` should equal the streamed data.
    pub compare_streamed: bool,

    pub events: Vec<Event>,

    /// Frames from `complete_frame` in `FrameFormat::MP4`, if accumulating.
    pub frames: Vec<Vec<u8>>,

    in_frame: bool,
    streamed: Vec<u8>,
    unit_start: Option<usize>,
}

impl CheckingHandler {
    pub fn new(accumulate: Accumulate, compare_streamed: bool) -> Self {
        Self {
            accumulate,
            compare_streamed,
            events: Vec::new(),
            frames: Vec::new(),
            in_frame: false,
            streamed: Vec::new(),
            unit_start: None,
        }
    }
}

impl VideoHandler<u64> for CheckingHandler {
    fn frame_start(&mut self, _frame_start: &mut VideoFrameStart<'_, u64>) -> Accumulate {
        assert!(!self.in_frame, "frame_start without frame_end or loss");
        self.in_frame = true;
        self.streamed.clear();
        self.unit_start = None;
        self.accumulate
    }

    fn data(&mut self, data: &VideoData<'_>) {
        assert!(self.in_frame, "data outside frame");
        assert_eq!(
            data.position.is_first(),
            self.unit_start.is_none(),
            "bad position {:?}",
            data.position
        );
        if data.position.is_first() {
            self.unit_start = Some(self.streamed.len());
            self.streamed.extend_from_slice(&[0; 4]);
        }
        for d in data.data {
            self.streamed.extend_from_slice(d);
        }
        if data.position.is_last() {
            let start = self.unit_start.take().unwrap();
            let len = u32::try_from(self.streamed.len() - start - 4).unwrap();
            self.streamed[start..start + 4].copy_from_slice(&len.to_be_bytes());
        }
        if matches!(data.position, Position::Complete | Position::Start) {
            assert!(!data.is_empty(), "first chunk should include header");
        }
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, u64>) {
        assert!(self.in_frame, "frame_end without frame_start");
        assert!(self.unit_start.is_none(), "frame ended mid-unit");
        self.in_frame = false;
        let mut visited = Vec::new();
        let visited_ok =
            frame_end.visit_frame_data(FrameFormat::MP4, &mut |c| visited.extend_from_slice(c));
        let frame = frame_end.complete_frame(FrameFormat::MP4);
        assert_eq!(frame.is_some(), self.accumulate == Accumulate::Yes);
        assert_eq!(visited_ok, frame.is_some());
        if let Some(frame) = frame {
            assert_eq!(visited, frame);
            if self.compare_streamed {
                assert_eq!(self.streamed, frame, "streamed data should match frame");
            }
            self.frames.push(frame);
        }
        self.events.push(Event::Frame {
            is_random_access_point: frame_end.is_random_access_point(),
            is_disposable: frame_end.is_disposable(),
            has_new_parameters: frame_end.has_new_parameters(),
            streamed: std::mem::take(&mut self.streamed),
        });
    }

    fn loss(&mut self, loss: &Loss<'_, u64>) {
        self.in_frame = false;
        self.unit_start = None;
        self.events.push(Event::Loss(loss.reason().clone()));
    }
}

/// Appends `payload` to `buf`, then pushes it to each depacketizer.
pub fn push(
    buf: &mut MarkBuf,
    meta: retina::rtp::ReceivedPacketMeta<u64>,
    payload: &[u8],
    targets: &mut [(&mut VideoDepacketizer<u64>, &mut CheckingHandler)],
) {
    let pos = buf.end();
    buf.extend(payload);
    buf.advance_unparsed(buf.end());
    let len = u16::try_from(payload.len()).expect("payload fits in u16");
    let pkt = ReceivedPacketRef::new(meta, buf, pos, len);
    for (d, h) in targets {
        d.push(&pkt, *h);
        d.check_invariants();
    }
}
