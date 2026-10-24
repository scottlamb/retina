// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`NalAnalyzer`], the interface of the H.264 and H.265 analyzers.

use crate::buf::MarkBuf;
use crate::codec::VideoParameters;

/// Analyzes H.264 or H.265 access units (frames), regardless of how they're
/// transported.
///
/// This is the codec layer beneath the RTP depacketizer
/// ([`crate::codec::VideoDepacketizer`]), implemented by
/// [`crate::codec::h264::Analyzer`] and [`crate::codec::h265::Analyzer`]. The
/// transport finds access unit boundaries and supplies each access unit's NAL
/// units; the analyzer tracks parameter sets and random access state across
/// access units and reports each to a [`crate::codec::VideoHandler`]: whether
/// each frame is a random access point, disposable, decodable given earlier
/// losses, and so on.
///
/// NAL units are supplied as byte ranges within a [`MarkBuf`]. The analyzer
/// marks the buffer to retain them while it needs them, so the transport can
/// read its input straight into the buffer and avoid copying. The transport
/// must supply only data it has parsed (before [`MarkBuf::unparsed`]), must
/// supply it in buffer order (as it naturally does when reading a stream into
/// the buffer), and must pass the same buffer to every call within an access
/// unit.
///
/// For each access unit, call:
///
/// 1.  [`NalAnalyzer::start_au`].
/// 2.  [`NalAnalyzer::push_nal`] for each NAL unit, in order, or
///     [`NalAnalyzer::start_nal`], [`NalAnalyzer::extend_nal`], and
///     [`NalAnalyzer::finish_nal`] to supply it in fragments as it arrives.
///     Optionally, the analyzer's `stream_with` after each to deliver
///     [`crate::codec::VideoHandler::frame_start`] and
///     [`crate::codec::VideoHandler::data`] events as early as possible.
/// 3.  The analyzer's `finish_au_with`.
///
/// A parameter set takes effect at the first slice that follows it. In
/// particular, one that follows an access unit's first slice applies starting
/// with the next access unit, so [`crate::codec::VideoFrameStart`] always
/// reports a frame's final parameters. (A parameter set there can't be for the
/// current picture; see H.264 sections 7.4.1.2.1 and 7.4.3, and H.265 sections
/// 7.4.2.4.2 and 7.4.7.1.)
pub(crate) trait NalAnalyzer<Ctx> {
    /// Returns the current parameters, if known.
    ///
    /// These may change as access units finish; see
    /// [`crate::codec::VideoFrameEnd::has_new_parameters`].
    fn parameters(&self) -> Option<&VideoParameters>;

    /// Starts an access unit.
    ///
    /// `ctx` will be supplied as [`crate::codec::VideoFrameStart::ctx`] and
    /// [`crate::codec::VideoFrameEnd::start_ctx`].
    ///
    /// # Panics
    ///
    /// Panics if an access unit is already in progress.
    fn start_au(&mut self, timestamp: crate::Timestamp, ctx: Ctx);

    /// Supplies a complete NAL unit, header included, at `[pos, pos + len)`
    /// within `buf`.
    ///
    /// This is equivalent to [`NalAnalyzer::start_nal`] followed by
    /// [`NalAnalyzer::finish_nal`].
    ///
    /// Returns an error if the NAL unit
    /// is shorter than its header, or as [`NalAnalyzer::start_nal`] does.
    ///
    /// # Panics
    ///
    /// As with [`NalAnalyzer::start_nal`].
    #[cfg_attr(not(test), allow(dead_code))]
    fn push_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), String>;

    /// Starts a NAL unit with the given `header` (1 byte for H.264, 2 bytes
    /// for H.265), supplying the first `body_len` bytes after it, at
    /// `[body_pos, body_pos + body_len)` within `buf`.
    ///
    /// The header is supplied separately as it may not be in `buf`, as when
    /// it's reconstructed from a fragmentation unit's headers.
    ///
    /// Supply the rest of the NAL unit, as it arrives, with
    /// [`NalAnalyzer::extend_nal`], then end it with
    /// [`NalAnalyzer::finish_nal`]. Each `stream_with` call in between
    /// delivers the data so far via [`crate::codec::VideoHandler::data`], so a
    /// large slice can be passed on while it's still arriving.
    ///
    /// Returns an error if the header is
    /// invalid. No NAL unit is started, and the access unit is otherwise
    /// unaffected; the caller may continue it or not.
    ///
    /// # Panics
    ///
    /// Panics if no access unit is in progress, if a NAL unit is already in
    /// progress, if the data isn't within `buf`'s parsed data, if it precedes
    /// data supplied earlier in the access unit, or if `buf` isn't the buffer
    /// supplied with this access unit's earlier data.
    fn start_nal(
        &mut self,
        header: &[u8],
        buf: &MarkBuf,
        body_pos: u64,
        body_len: usize,
    ) -> Result<(), String>;

    /// Supplies more of the NAL unit begun by [`NalAnalyzer::start_nal`]: the
    /// `len` bytes at `[pos, pos + len)` within `buf`.
    ///
    /// Returns an error if the NAL unit
    /// would become too large to represent; the NAL unit is unaffected.
    ///
    /// # Panics
    ///
    /// Panics if no NAL unit is in progress, or as with
    /// [`NalAnalyzer::start_nal`].
    fn extend_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), String>;

    /// Ends the NAL unit begun by [`NalAnalyzer::start_nal`].
    ///
    /// Currently this can't fail; it returns a `Result` to allow future
    /// validation.
    ///
    /// # Panics
    ///
    /// Panics if no NAL unit is in progress.
    fn finish_nal(&mut self) -> Result<(), String>;
}
