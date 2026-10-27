// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`NalAnalyzer`], the interface of the H.264 and H.265 analyzers.

use crate::buf::MarkBuf;
use crate::codec::{Error, VideoHandler, VideoParameters};

/// Analyzes H.264 or H.265 access units (frames), regardless of how they're
/// transported.
///
/// This is the codec layer beneath the RTP depacketizer
/// ([`crate::codec::VideoDepacketizer`]), exposed for transports Retina doesn't
/// handle itself, such as FLV or MPEG-TS. It's implemented by
/// [`crate::codec::h264::Analyzer`] and [`crate::codec::h265::Analyzer`]. The
/// transport finds access unit boundaries and supplies each access unit's NAL
/// units; the analyzer tracks parameter sets and random access state across
/// access units and reports each to a [`VideoHandler`], with the same events
/// and metadata the RTP depacketizer produces: whether each frame is a random
/// access point, disposable, decodable given earlier losses, and so on.
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
///     Optionally, [`NalAnalyzer::stream`] after each to deliver
///     [`VideoHandler::frame_start`] and [`VideoHandler::data`] events as
///     early as possible.
/// 3.  [`NalAnalyzer::finish_au`].
///
/// Between access units, supply any parameter sets received out-of-band
/// (such as in an FLV or MP4 `AVCDecoderConfigurationRecord`) via
/// [`NalAnalyzer::push_parameter_set`].
///
/// If input is lost, call [`NalAnalyzer::discontinuity`], which also abandons
/// any access unit in progress.
///
/// A parameter set takes effect at the first slice that follows it, whether
/// it arrives in-band or out-of-band. In particular, one that follows an
/// access unit's first slice applies starting with the next access unit, so
/// [`crate::codec::VideoFrameStart`] always reports a frame's final
/// parameters. (A parameter set there can't be for the current picture; see
/// H.264 sections 7.4.1.2.1 and 7.4.3, and H.265 sections 7.4.2.4.2 and
/// 7.4.7.1.)
///
/// ```
/// # #[cfg(feature = "unstable-codec-analyzer")]
/// # fn f(
/// #     buf: &retina::buf::MarkBuf,
/// #     nals: &[(u64, usize)],
/// #     timestamp: retina::Timestamp,
/// #     handler: &mut impl retina::codec::VideoHandler<u64>,
/// # ) -> Result<(), retina::codec::Error> {
/// use retina::codec::{h264, h26x::NalAnalyzer as _};
/// let mut analyzer = h264::Analyzer::new();
/// let ctx = 0u64; // a caller-chosen context, such as a byte offset.
/// analyzer.start_au(timestamp, ctx);
/// for &(pos, len) in nals {
///     analyzer.push_nal(buf, pos, len)?;
/// }
/// analyzer.finish_au(buf, &ctx, handler);
/// # Ok(())
/// # }
/// ```
///
/// This trait is dyn-compatible, so a transport which learns the codec at
/// runtime can hold a `Box<dyn NalAnalyzer<Ctx>>`:
///
/// ```
/// # #[cfg(feature = "unstable-codec-analyzer")]
/// # fn f(h265: bool) {
/// use retina::codec::{h264, h265, h26x::NalAnalyzer};
/// let analyzer: Box<dyn NalAnalyzer<u64>> = if h265 {
///     Box::new(h265::Analyzer::new())
/// } else {
///     Box::new(h264::Analyzer::new())
/// };
/// # }
/// ```
#[cfg_attr(not(feature = "unstable-codec-analyzer"), allow(dead_code))]
pub trait NalAnalyzer<Ctx> {
    /// Returns the current parameters, if known.
    ///
    /// These may change as access units finish; see
    /// [`crate::codec::VideoFrameEnd::has_new_parameters`].
    fn parameters(&self) -> Option<&VideoParameters>;

    /// Supplies a parameter set NAL unit (header included) received
    /// out-of-band, such as in an FLV or MP4 `AVCDecoderConfigurationRecord`
    /// or `HEVCDecoderConfigurationRecord` (ISO/IEC 14496-15). It takes effect
    /// at the next access unit's first slice.
    ///
    /// The H.264 and H.265 specs allow conveying parameter sets this way, as
    /// long as they're available in time for the pictures which refer to them
    /// (H.264 section 7.4.1.2.1 NOTE 1 and NOTE 4; H.265 section 7.4.2.4.2
    /// NOTE 1 and NOTE 4).
    ///
    /// Returns an [`crate::codec::ErrorKind::Invalid`] error if `nal` doesn't
    /// have a valid header for a parameter set Retina tracks (H.264 SPS or
    /// PPS; H.265 VPS, SPS, or PPS). Errors parsing the parameter set are
    /// reported as for in-band parameter sets, by the next access unit's
    /// [`NalAnalyzer::finish_au`].
    ///
    /// # Panics
    ///
    /// Panics if an access unit is in progress.
    fn push_parameter_set(&mut self, nal: &[u8]) -> Result<(), Error>;

    /// Starts an access unit.
    ///
    /// `ctx` will be supplied as [`crate::codec::VideoFrameStart::ctx`] and
    /// [`crate::codec::VideoFrameEnd::start_ctx`].
    ///
    /// # Panics
    ///
    /// Panics if an access unit is already in progress.
    fn start_au(&mut self, timestamp: crate::Timestamp, ctx: Ctx);

    /// Notes RTP header extension values for the access unit in progress,
    /// as from each of its packets.
    ///
    /// Values already noted take precedence. They're supplied as
    /// [`crate::codec::VideoFrameStart::extensions`] (if the frame hasn't
    /// started yet) and [`crate::codec::VideoFrameEnd::extensions`]. A
    /// non-RTP transport can use this to supply equivalent values, such as
    /// a capture time.
    ///
    /// # Panics
    ///
    /// Panics if no access unit is in progress.
    #[cfg(feature = "unstable-extensions")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable-extensions")))]
    fn add_extensions(&mut self, extensions: &crate::rtp::Extensions);

    /// Supplies a complete NAL unit, header included, at `[pos, pos + len)`
    /// within `buf`.
    ///
    /// This is equivalent to [`NalAnalyzer::start_nal`] followed by
    /// [`NalAnalyzer::finish_nal`].
    ///
    /// Returns an [`crate::codec::ErrorKind::Invalid`] error if the NAL unit
    /// is shorter than its header, or as [`NalAnalyzer::start_nal`] does.
    ///
    /// # Panics
    ///
    /// As with [`NalAnalyzer::start_nal`].
    fn push_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), Error>;

    /// Starts a NAL unit with the given `header` (1 byte for H.264, 2 bytes
    /// for H.265), supplying the first `body_len` bytes after it, at
    /// `[body_pos, body_pos + body_len)` within `buf`.
    ///
    /// The header is supplied separately as it may not be in `buf`, as when
    /// it's reconstructed from a fragmentation unit's headers.
    ///
    /// Supply the rest of the NAL unit, as it arrives, with
    /// [`NalAnalyzer::extend_nal`], then end it with
    /// [`NalAnalyzer::finish_nal`]. Each [`NalAnalyzer::stream`] call in
    /// between delivers the data so far via [`VideoHandler::data`], so a large
    /// slice can be passed on while it's still arriving.
    ///
    /// Returns an [`crate::codec::ErrorKind::Invalid`] error if the header is
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
    ) -> Result<(), Error>;

    /// Supplies more of the NAL unit begun by [`NalAnalyzer::start_nal`]: the
    /// `len` bytes at `[pos, pos + len)` within `buf`.
    ///
    /// Returns an [`crate::codec::ErrorKind::Invalid`] error if the NAL unit
    /// would become too large to represent; the NAL unit is unaffected.
    ///
    /// # Panics
    ///
    /// Panics if no NAL unit is in progress, or as with
    /// [`NalAnalyzer::start_nal`].
    fn extend_nal(&mut self, buf: &MarkBuf, pos: u64, len: usize) -> Result<(), Error>;

    /// Ends the NAL unit begun by [`NalAnalyzer::start_nal`].
    ///
    /// Currently this can't fail; it returns a `Result` to allow future
    /// validation.
    ///
    /// # Panics
    ///
    /// Panics if no NAL unit is in progress.
    fn finish_nal(&mut self) -> Result<(), Error>;

    /// Starts the frame if possible and delivers its data so far.
    ///
    /// This is optional; [`NalAnalyzer::finish_au`] does the same. Calling it
    /// after each NAL unit or fragment delivers events with lower latency,
    /// and with [`crate::codec::Accumulate::No`] releases the buffer data
    /// supplied so far.
    fn stream(&mut self, buf: &MarkBuf, handler: &mut dyn VideoHandler<Ctx>);

    /// Finishes the current access unit, delivering any remaining events to
    /// `handler`.
    ///
    /// `end_ctx` will be supplied as [`crate::codec::VideoFrameEnd::end_ctx`].
    /// If the access unit is invalid (for example, it has an invalid
    /// parameter set, or a NAL unit is still in progress), reports
    /// [`crate::codec::LossReason::Corrupt`] to [`VideoHandler::loss`] instead
    /// of finishing the frame. An access unit without slices produces no
    /// events.
    ///
    /// # Panics
    ///
    /// Panics if no access unit is in progress.
    fn finish_au(&mut self, buf: &MarkBuf, end_ctx: &Ctx, handler: &mut dyn VideoHandler<Ctx>);

    /// Notes that input was lost (such as on reconnecting), discarding any
    /// in-progress access unit and reporting
    /// [`crate::codec::LossReason::Discontinuity`].
    ///
    /// Frames are then undecodable until the next random access point.
    fn discontinuity(&mut self, ctx: &Ctx, handler: &mut dyn VideoHandler<Ctx>);
}
