// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Packetization of H.264 ([RFC 6184](https://tools.ietf.org/html/rfc6184)
//! packetization mode 1) and H.265 ([RFC 7798](https://tools.ietf.org/html/rfc7798))
//! NAL units.
//!
//! The two formats have the same structure: single NAL unit packets,
//! aggregation packets (H.264 STAP-A; H.265 AP), and fragmentation units
//! (H.264 FU-A; H.265 FU). They differ only in header layouts, which
//! [`Codec`] describes.

use bytes::Bytes;

use crate::codec::Error;
use crate::codec::{
    ParameterSetInsertion, Payload, PayloadFormat, PayloadSink, Position, VideoFrameInfo,
    VideoPacketizerOptions, VideoParameters,
};

/// Codec-specific parts of packetization.
pub(crate) trait Codec {
    /// A NAL header: `[u8; 1]` for H.264, `[u8; 2]` for H.265.
    type Header: Copy + Default + std::fmt::Debug + AsRef<[u8]> + AsMut<[u8]>;

    /// A fragmentation unit's headers: the payload header (H.264's FU
    /// indicator), then the FU header.
    type FuHeader: AsRef<[u8]>;

    /// The number of parameter sets: SPS and PPS for H.264; VPS, SPS, and PPS
    /// for H.265.
    const PARAMETER_SETS: usize;

    /// Returns the parameter sets within `parameters`, in insertion order, or
    /// `None` if they're for a different codec.
    fn parameter_sets(parameters: &VideoParameters) -> Option<Vec<Bytes>>;

    /// Returns parameters for the given parameter sets, in insertion order.
    fn parameters(sets: &[&[u8]]) -> Result<VideoParameters, crate::codec::Error>;

    /// Returns a description of the stream, with parameter sets as in
    /// [`Codec::parameter_sets`].
    fn payload_format(parameters: &VideoParameters, sets: &[Bytes]) -> PayloadFormat;

    /// Returns the index into [`Codec::parameter_sets`] of a NAL with the
    /// given header, if it's a parameter set.
    fn parameter_set_index(hdr: Self::Header) -> Option<usize>;

    /// Returns why a NAL with the given header can't be packetized, if it
    /// can't, for reasons other than its F bit; see
    /// [`Packetizer::invalid_header`].
    ///
    /// NAL types which are unspecified by the codec and used by the RTP
    /// payload format for aggregation and fragmentation packets are invalid;
    /// the packetizer rejects or discards these rather than send ambiguous
    /// packets.
    fn invalid_header(hdr: Self::Header) -> Option<&'static str>;

    /// Returns the payload header for an aggregation packet containing NALs
    /// with the headers `a` and `b`, either of which may itself be an
    /// aggregation packet's payload header.
    fn aggregation_header(a: Self::Header, b: Self::Header) -> Self::Header;

    /// Returns the headers of a fragment of a NAL with header `hdr`.
    fn fu_header(hdr: Self::Header, start: bool, end: bool) -> Self::FuHeader;

    /// Returns true if a NAL with the given header is a VCL NAL.
    fn is_vcl(hdr: Self::Header) -> bool;

    /// Returns true if a NAL with the given header is an access unit
    /// delimiter, which must be first in its access unit.
    fn is_access_unit_delimiter(hdr: Self::Header) -> bool;

    /// Returns true if a NAL with the given header is an end of sequence or
    /// end of stream NAL, which can be followed by nothing else in its access
    /// unit (except an end of stream NAL).
    fn ends_sequence(hdr: Self::Header) -> bool;

    /// Returns the header of a filler data NAL for an access unit whose most
    /// recent VCL NAL had header `vcl`, if any.
    fn filler_header(vcl: Option<Self::Header>) -> Self::Header;
}

/// The body of a minimal filler data NAL: no `0xff` bytes, just
/// `rbsp_trailing_bits`. This is the same for H.264 and H.265.
const FILLER_BODY: [u8; 1] = [0x80];

/// Packetizes NAL units. See [`crate::codec::VideoPacketizer`].
///
/// To set the marker bit, the most recent payload is held back until the next
/// input shows it isn't the last of its frame, or until the caller flushes
/// it. Held payloads are copied into `held`; other payloads (all but the last
/// fragment of each fragmented NAL) are delivered with data referring directly
/// to the input, except for a remainder of less than one payload at the end of
/// each input chunk.
#[derive(Debug)]
pub(crate) struct Packetizer<C: Codec> {
    /// The current frame's maximum payload size, from the sink at its start.
    max_payload_size: usize,

    aggregate: bool,
    parameter_set_insertion: ParameterSetInsertion,

    parameters: VideoParameters,

    /// The parameter sets within `parameters`, as in [`Codec::parameter_sets`].
    parameter_sets: Vec<Bytes>,

    /// True if parameters have changed since they were last inserted.
    parameters_changed: bool,

    /// True if the current frame has reached neither its insertion point nor
    /// a congestion drop. See "Parameter sets" on
    /// [`crate::codec::VideoPacketizer`].
    insertion_pending: bool,

    /// Parameter sets supplied in-band but not yet applied, by index as in
    /// [`Codec::parameter_sets`].
    new_sets: Vec<Option<Vec<u8>>>,

    /// In-band parameter sets which couldn't be parsed, to pass through as-is
    /// at the next insertion point.
    unparsed_sets: Vec<Vec<u8>>,

    /// True if the current frame has passed through a changed parameter set
    /// after its insertion point.
    late_sets_delivered: bool,

    /// The in-band parameter set currently being supplied, if any: its index
    /// as in [`Codec::parameter_sets`] and its data so far, header included.
    set_unit: Option<(usize, Vec<u8>)>,

    /// True if in-band parameter sets couldn't be parsed, so as to log only
    /// once.
    seen_unparsed_sets: bool,

    frame: Option<VideoFrameInfo>,

    /// True if no payload of `frame` has been delivered yet.
    frame_start_pending: bool,

    /// The NAL currently being supplied, if any.
    nal: Option<PacketizerNal<C::Header>>,

    /// A complete payload which hasn't been delivered yet, or empty.
    held: Vec<u8>,
    held_kind: HeldKind,

    /// The header of the last NAL in `held`, if `held_kind` isn't `None`.
    held_last_hdr: C::Header,

    /// True if the most recently delivered payload was released unmarked by
    /// `flush`, so the frame's end needs a filler NAL to carry the marker bit.
    flushed: bool,

    /// The header of the current frame's most recent VCL NAL, if any.
    frame_vcl_hdr: Option<C::Header>,

    /// True if a VCL NAL of the current frame has ended, so `held` (if
    /// anything) includes it or a later NAL.
    frame_vcl_ended: bool,

    /// An empty buffer to reuse for the next `PacketizerNal::buffered`.
    spare: Vec<u8>,

    /// True if the rest of the current unit is being discarded; see
    /// [`Codec::invalid_header`].
    discarding_unit: bool,

    /// True if a unit has been discarded, so as to log only once.
    seen_invalid_nal: bool,

    /// True if the caller has misused `push_unit` or `end_frame`, so as to
    /// log only once.
    seen_misuse: bool,

    /// True if the rest of the current frame is being dropped due to congestion.
    dropping_frame: bool,

    /// True if frames are being dropped until the next random access point,
    /// because a frame others may depend on was dropped or data was lost.
    awaiting_rap: bool,
}

#[derive(Debug)]
struct PacketizerNal<H> {
    hdr: H,

    /// Body bytes (excluding the header) which haven't been delivered yet.
    buffered: Vec<u8>,

    /// True if a start fragment has been delivered.
    fragmenting: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum HeldKind {
    None,

    /// A single NAL unit packet, which may still become part of an aggregation packet.
    Single,

    /// An aggregation packet which may be extended.
    Aggregation,

    /// The final fragment of a fragmented NAL.
    FuEnd,

    /// The final payload of a NAL truncated due to congestion.
    Truncated,
}

impl<C: Codec> Packetizer<C> {
    const HDR_LEN: usize = size_of::<C::Header>();
    const FU_HDR_LEN: usize = size_of::<C::FuHeader>();

    pub(crate) fn new(
        parameters: &VideoParameters,
        options: VideoPacketizerOptions,
    ) -> Result<Self, Error> {
        let Some(parameter_sets) = C::parameter_sets(parameters) else {
            return Err(Error::invalid(format!(
                "parameters are for a different codec: {}",
                parameters.rfc6381_codec()
            )));
        };
        Ok(Self {
            max_payload_size: 1400, // `PayloadSink::max_payload_size`'s default.
            aggregate: options.aggregate,
            parameter_set_insertion: options.parameter_set_insertion,
            parameters: parameters.clone(),
            parameter_sets,
            parameters_changed: false,
            insertion_pending: false,
            new_sets: vec![None; C::PARAMETER_SETS],
            unparsed_sets: Vec::new(),
            late_sets_delivered: false,
            set_unit: None,
            seen_unparsed_sets: false,
            frame: None,
            frame_start_pending: false,
            nal: None,
            held: Vec::new(),
            held_kind: HeldKind::None,
            held_last_hdr: C::Header::default(),
            flushed: false,
            frame_vcl_hdr: None,
            frame_vcl_ended: false,
            spare: Vec::new(),
            discarding_unit: false,
            seen_invalid_nal: false,
            seen_misuse: false,
            dropping_frame: false,
            awaiting_rap: false,
        })
    }

    pub(crate) fn parameters(&self) -> &VideoParameters {
        &self.parameters
    }

    pub(crate) fn payload_format(&self) -> PayloadFormat {
        C::payload_format(&self.parameters, &self.parameter_sets)
    }

    /// Returns the payload format for `parameters`, or `None` if they're for
    /// a different codec.
    pub(crate) fn payload_format_for(parameters: &VideoParameters) -> Option<PayloadFormat> {
        C::parameter_sets(parameters).map(|sets| C::payload_format(parameters, &sets))
    }

    pub(crate) fn set_parameters(&mut self, parameters: &VideoParameters) -> Result<(), Error> {
        if *parameters == self.parameters {
            return Ok(());
        }
        let Some(parameter_sets) = C::parameter_sets(parameters) else {
            return Err(Error::invalid(format!(
                "parameters are for a different codec: {}",
                parameters.rfc6381_codec()
            )));
        };
        if parameter_sets != self.parameter_sets {
            self.parameter_sets = parameter_sets;
            self.parameters_changed = true;
        }
        self.parameters = parameters.clone();
        Ok(())
    }

    pub(crate) fn start_frame(&mut self, frame: VideoFrameInfo, sink: &mut impl PayloadSink) {
        if self.frame.is_some() {
            self.end_frame(sink);
        }
        // The minimum makes progress with fragments.
        self.max_payload_size = usize::from(sink.max_payload_size()).max(Self::FU_HDR_LEN + 1);
        self.frame = Some(frame);
        self.frame_start_pending = true;
        self.frame_vcl_hdr = None;
        self.frame_vcl_ended = false;
        self.late_sets_delivered = false;
        if (self.awaiting_rap && !frame.is_random_access_point) || sink.congested() {
            tracing::trace!("dropping frame {frame:?}");
            self.drop_rest_of_frame();
            return;
        }
        self.awaiting_rap = false;
        self.insertion_pending = true;
    }

    /// Inserts parameter sets as due, at the frame's insertion point.
    ///
    /// This applies the in-band parameter sets supplied before it, so they
    /// take effect for this frame.
    fn insert_parameter_sets(&mut self, sink: &mut impl PayloadSink) {
        if !std::mem::take(&mut self.insertion_pending) {
            return;
        }
        self.apply_new_sets(true);
        let frame = self.frame.as_ref().expect("insertion within frame");
        let insert = match self.parameter_set_insertion {
            ParameterSetInsertion::EachKeyFrame => {
                frame.is_random_access_point || self.parameters_changed
            }
            ParameterSetInsertion::OnChange => self.parameters_changed,
            ParameterSetInsertion::Never => false,
        };
        if insert {
            self.parameters_changed = false;
            for set in self.parameter_sets.clone() {
                self.push_nal(Position::Complete, &[&set], sink);
            }
        }
        for set in std::mem::take(&mut self.unparsed_sets) {
            self.push_nal(Position::Complete, &[&set], sink);
        }
    }

    /// Applies in-band parameter sets supplied since the last call.
    ///
    /// If they can't be parsed, the parameters are unchanged, and (if
    /// `pass_through`) the sets are passed through at the next insertion
    /// point, so receivers still get them.
    fn apply_new_sets(&mut self, pass_through: bool) {
        let new_sets = std::mem::replace(&mut self.new_sets, vec![None; C::PARAMETER_SETS]);
        if !new_sets
            .iter()
            .zip(&self.parameter_sets)
            .any(|(new, old)| new.as_ref().is_some_and(|n| n[..] != old[..]))
        {
            return;
        }
        let merged: Vec<&[u8]> = new_sets
            .iter()
            .zip(&self.parameter_sets)
            .map(|(new, old)| new.as_deref().unwrap_or(&old[..]))
            .collect();
        match C::parameters(&merged) {
            Ok(p) => self
                .set_parameters(&p)
                .expect("parameters from parameter sets are for the same codec"),
            Err(e) => {
                if !self.seen_unparsed_sets {
                    tracing::warn!(
                        error = %e,
                        "Passing through in-band parameter sets which can't be parsed; \
                         will not log about this again for this stream"
                    );
                    self.seen_unparsed_sets = true;
                }
                if pass_through {
                    self.unparsed_sets.extend(new_sets.into_iter().flatten());
                }
            }
        }
    }

    /// Ends the in-band parameter set in progress.
    ///
    /// Before the insertion point, the set is held to apply there. After it,
    /// the set is passed through as-is if it changes the parameters, as it
    /// can't be moved before the NALs already delivered; it's applied when
    /// the frame ends.
    fn end_set_unit(&mut self, sink: &mut impl PayloadSink) {
        let (i, set) = self.set_unit.take().expect("set unit in progress");
        let late = !self.insertion_pending && !self.dropping_frame;
        if late
            && self.new_sets[i]
                .as_deref()
                .unwrap_or(&self.parameter_sets[i][..])
                != &set[..]
        {
            self.push_nal(Position::Complete, &[&set], sink);
            self.late_sets_delivered |= !self.dropping_frame;
        }
        self.new_sets[i] = Some(set);
    }

    /// Returns why a NAL with the given header can't be packetized, if it
    /// can't.
    ///
    /// The F bit (H.264 and H.265 `forbidden_zero_bit`) marks a damaged NAL.
    /// Receivers including Retina's own depacketizer reject these, so rather
    /// than pass damage through, callers should report lost data via
    /// `discontinuity`. (The packetizer itself sets the F bit on NALs it
    /// truncates for congestion.)
    fn invalid_header(hdr: C::Header) -> Option<&'static str> {
        if hdr.as_ref()[0] & 0b1000_0000 != 0 {
            return Some("F bit set");
        }
        C::invalid_header(hdr)
    }

    /// Returns the header at the start of `data`, if it's long enough.
    fn header(data: &[&[u8]]) -> Option<C::Header> {
        let mut hdr = C::Header::default();
        let mut filled = 0;
        for d in data {
            let n = d.len().min(Self::HDR_LEN - filled);
            hdr.as_mut()[filled..filled + n].copy_from_slice(&d[..n]);
            filled += n;
            if filled == Self::HDR_LEN {
                return Some(hdr);
            }
        }
        None
    }

    /// Notes misuse by the caller, logging only the first time.
    fn misuse(&mut self, what: &str) {
        if !self.seen_misuse {
            tracing::warn!("{what}; will not log about misuse again for this stream");
            self.seen_misuse = true;
        }
    }

    pub(crate) fn push_unit(
        &mut self,
        position: Position,
        data: &[&[u8]],
        sink: &mut impl PayloadSink,
    ) {
        if self.frame.is_none() {
            self.misuse("codec unit data supplied outside a frame; discarding");
            return;
        }
        if position.is_first() {
            if self.set_unit.is_some() {
                self.misuse("codec unit started while another is in progress; ending the other");
                self.end_set_unit(sink);
            }
            let hdr = Self::header(data);
            if let Some(i) = hdr
                .filter(|&h| Self::invalid_header(h).is_none())
                .and_then(C::parameter_set_index)
            {
                if self.nal.is_some() {
                    self.misuse(
                        "codec unit started while another is in progress; ending the other",
                    );
                    self.end_nal(sink);
                }
                self.discarding_unit = false;
                self.set_unit = Some((i, data.concat()));
                if position.is_last() {
                    self.end_set_unit(sink);
                }
                return;
            }
            if !hdr.is_some_and(C::is_access_unit_delimiter) {
                self.insert_parameter_sets(sink);
            }
        } else if let Some((_, set)) = &mut self.set_unit {
            for d in data {
                set.extend_from_slice(d);
            }
            if position.is_last() {
                self.end_set_unit(sink);
            }
            return;
        }
        self.push_nal(position, data, sink);
    }

    /// Supplies a chunk of a NAL other than an in-band parameter set.
    fn push_nal(&mut self, position: Position, data: &[&[u8]], sink: &mut impl PayloadSink) {
        if self.dropping_frame {
            return;
        }
        let mut data = data.iter().copied().filter(|d| !d.is_empty());
        if position.is_first() {
            if self.nal.is_some() {
                self.misuse("codec unit started while another is in progress; ending the other");
                self.end_nal(sink);
            }
            self.discarding_unit = false;

            // Gather the header, which may span chunks.
            let mut hdr = C::Header::default();
            let mut filled = 0;
            let mut rest: &[u8] = &[];
            while filled < Self::HDR_LEN {
                let Some(d) = data.next() else {
                    break;
                };
                let n = d.len().min(Self::HDR_LEN - filled);
                hdr.as_mut()[filled..filled + n].copy_from_slice(&d[..n]);
                filled += n;
                rest = &d[n..];
            }
            let invalid = if filled == 0 {
                Some("no data")
            } else if filled < Self::HDR_LEN {
                Some("truncated header")
            } else {
                Self::invalid_header(hdr)
            };
            if let Some(reason) = invalid {
                if !self.seen_invalid_nal {
                    tracing::warn!(
                        nal_header = format_args!("{:02x?}", &hdr.as_ref()[..filled]),
                        reason,
                        "Discarding invalid NAL; will not log about this again for this stream",
                    );
                    self.seen_invalid_nal = true;
                }
                self.discarding_unit = !position.is_last();
                return;
            }
            if sink.congested() {
                // Truncate this NAL to just its header.
                self.flush_held(false, sink);
                self.held.clear();
                self.held.extend_from_slice(damaged(hdr).as_ref());
                self.held_kind = HeldKind::Truncated;
                self.drop_rest_of_frame();
                return;
            }
            if C::is_vcl(hdr) {
                self.frame_vcl_hdr = Some(hdr);
            }
            self.nal = Some(PacketizerNal {
                hdr,
                buffered: std::mem::take(&mut self.spare),
                fragmenting: false,
            });
            self.feed(rest, sink);
        } else if self.discarding_unit {
            self.discarding_unit = !position.is_last();
            return;
        } else if self.nal.is_none() {
            self.misuse("codec unit continued without being started; discarding");
            return;
        }
        for d in data {
            if self.dropping_frame {
                return;
            }
            self.feed(d, sink);
        }
        if self.dropping_frame {
            return;
        }
        if position.is_last() {
            self.end_nal(sink);
        }
    }

    /// Supplies body bytes of the current NAL, delivering any fragments
    /// which are known not to be its last.
    fn feed(&mut self, mut input: &[u8], sink: &mut impl PayloadSink) {
        let max = self.max_payload_size;
        loop {
            let nal = self.nal.as_mut().expect("feed with NAL in progress");

            // Body bytes which fit in the current packet type: a fragment
            // (after its headers) or a single NAL unit packet (after the NAL
            // header).
            let limit = max
                - if nal.fragmenting {
                    Self::FU_HDR_LEN
                } else {
                    Self::HDR_LEN
                };
            let total = nal.buffered.len() + input.len();
            if total <= limit {
                nal.buffered.extend_from_slice(input);
                return;
            }

            if sink.congested() {
                self.truncate(input, sink);
                return;
            }
            let nal = self.nal.as_mut().expect("feed with NAL in progress");

            // This NAL must be fragmented, and there's more than a fragment's worth
            // of data, so the next fragment isn't the last.
            let header = C::fu_header(nal.hdr, !nal.fragmenting, false);
            nal.fragmenting = true;
            let body_len = max - Self::FU_HDR_LEN;
            let from_buffered = nal.buffered.len().min(body_len);
            let from_input = body_len - from_buffered;
            let mut buffered = std::mem::take(&mut nal.buffered);
            self.flush_held(false, sink);
            self.deliver(
                &[
                    header.as_ref(),
                    &buffered[..from_buffered],
                    &input[..from_input],
                ],
                false,
                sink,
            );
            buffered.drain(..from_buffered);
            input = &input[from_input..];
            self.nal.as_mut().unwrap().buffered = buffered;
        }
    }

    /// Truncates the current NAL, of which `nal.buffered` and `input` are the
    /// next body bytes, then drops the rest of the frame.
    ///
    /// The NAL's final payload is the one which would otherwise have been
    /// delivered next, but with the F bit set (and, if fragmenting, the end
    /// bit). It's held so that `end_frame` delivers it with the marker bit.
    fn truncate(&mut self, input: &[u8], sink: &mut impl PayloadSink) {
        let mut nal = self.nal.take().expect("truncate with NAL in progress");
        tracing::trace!(
            nal_header = format_args!("{:02x?}", nal.hdr),
            "truncating NAL"
        );
        self.flush_held(false, sink);
        self.held.clear();
        let hdr = damaged(nal.hdr);
        if nal.fragmenting {
            self.held
                .extend_from_slice(C::fu_header(hdr, false, true).as_ref());
        } else {
            self.held.extend_from_slice(hdr.as_ref());
        }
        let body_limit = self.max_payload_size - self.held.len();
        let from_buffered = nal.buffered.len().min(body_limit);
        let from_input = input.len().min(body_limit - from_buffered);
        self.held.extend_from_slice(&nal.buffered[..from_buffered]);
        self.held.extend_from_slice(&input[..from_input]);
        self.held_kind = HeldKind::Truncated;
        nal.buffered.clear();
        self.spare = nal.buffered;
        self.drop_rest_of_frame();
    }

    /// Drops the rest of the current frame, and (unless it's disposable)
    /// following frames until the next random access point.
    fn drop_rest_of_frame(&mut self) {
        let frame = self
            .frame
            .as_ref()
            .expect("drop_rest_of_frame within frame");
        self.dropping_frame = true;
        self.insertion_pending = false;
        self.awaiting_rap |= !frame.is_disposable;
        self.nal = None;
        self.discarding_unit = false;
    }

    /// Ends the current NAL.
    fn end_nal(&mut self, sink: &mut impl PayloadSink) {
        let mut nal = self.nal.take().expect("end_nal with NAL in progress");
        self.end_nal_inner(&nal, sink);
        nal.buffered.clear();
        self.spare = nal.buffered;
    }

    fn end_nal_inner(&mut self, nal: &PacketizerNal<C::Header>, sink: &mut impl PayloadSink) {
        // `flush_held` below doesn't look at these, so it's fine to set early.
        self.held_last_hdr = nal.hdr;
        self.frame_vcl_ended |= C::is_vcl(nal.hdr);
        if nal.fragmenting {
            // `feed` always leaves at least one byte for the end fragment.
            debug_assert!(!nal.buffered.is_empty());
            self.flush_held(false, sink);
            self.held.clear();
            self.held
                .extend_from_slice(C::fu_header(nal.hdr, false, true).as_ref());
            self.held.extend_from_slice(&nal.buffered);
            self.held_kind = HeldKind::FuEnd;
            return;
        }
        let len = Self::HDR_LEN + nal.buffered.len();
        debug_assert!(len <= self.max_payload_size);
        match self.held_kind {
            HeldKind::Single
                if self.aggregate
                    && Self::HDR_LEN + 2 + self.held.len() + 2 + len <= self.max_payload_size =>
            {
                // Convert the held single NAL unit packet into an aggregation packet.
                let held_len = u16::try_from(self.held.len()).expect("payload fits in u16");
                let hdr = C::aggregation_header(self.held_header(), nal.hdr);
                self.held.splice(
                    0..0,
                    hdr.as_ref().iter().copied().chain(held_len.to_be_bytes()),
                );
                self.append_to_aggregation(nal);
                return;
            }
            HeldKind::Aggregation
                if self.aggregate && self.held.len() + 2 + len <= self.max_payload_size =>
            {
                let hdr = C::aggregation_header(self.held_header(), nal.hdr);
                self.held[..Self::HDR_LEN].copy_from_slice(hdr.as_ref());
                self.append_to_aggregation(nal);
                return;
            }
            _ => {}
        }
        self.flush_held(false, sink);
        self.held.clear();
        self.held.extend_from_slice(nal.hdr.as_ref());
        self.held.extend_from_slice(&nal.buffered);
        self.held_kind = HeldKind::Single;
    }

    /// Returns the header at the start of the held payload: a NAL header or
    /// an aggregation packet's payload header.
    fn held_header(&self) -> C::Header {
        let mut hdr = C::Header::default();
        hdr.as_mut().copy_from_slice(&self.held[..Self::HDR_LEN]);
        hdr
    }

    fn append_to_aggregation(&mut self, nal: &PacketizerNal<C::Header>) {
        let len = u16::try_from(Self::HDR_LEN + nal.buffered.len()).expect("NAL fits in u16");
        self.held.extend_from_slice(&len.to_be_bytes());
        self.held.extend_from_slice(nal.hdr.as_ref());
        self.held.extend_from_slice(&nal.buffered);
        self.held_kind = HeldKind::Aggregation;
    }

    /// Delivers the held payload, if any.
    fn flush_held(&mut self, mark: bool, sink: &mut impl PayloadSink) {
        if self.held_kind == HeldKind::None {
            return;
        }
        let held = std::mem::take(&mut self.held);
        self.deliver(&[&held], mark, sink);
        self.held = held;
        self.held.clear();
        self.held_kind = HeldKind::None;
    }

    fn deliver(&mut self, data: &[&[u8]], mark: bool, sink: &mut impl PayloadSink) {
        let frame = self.frame.as_ref().expect("deliver within frame");
        let first = std::mem::take(&mut self.frame_start_pending);
        self.flushed = false;
        sink.payload(&Payload {
            timestamp: frame.timestamp,
            position: Position::new(first, mark),
            data,
            is_random_access_point: frame.is_random_access_point,
            is_disposable: frame.is_disposable,
        });
    }

    /// Delivers the held payload now, unless it must carry the marker bit.
    ///
    /// The held payload is made of complete NALs (or a NAL's final fragment);
    /// data of a NAL still in progress waits for the rest of that NAL. NALs
    /// before the frame's first VCL NAL also wait, as a VCL NAL must follow
    /// them, and they may be aggregated with it.
    pub(crate) fn flush(&mut self, sink: &mut impl PayloadSink) {
        match self.held_kind {
            HeldKind::None => {}
            _ if !self.frame_vcl_ended => {}

            // A truncated NAL ends its frame, so it can be marked now.
            HeldKind::Truncated => self.flush_held(true, sink),

            // Nothing can follow this NAL to carry the marker bit.
            _ if C::ends_sequence(self.held_last_hdr) => {}

            _ => {
                self.flush_held(false, sink);
                self.flushed = true;
            }
        }
    }

    pub(crate) fn end_frame(&mut self, sink: &mut impl PayloadSink) {
        if self.frame.is_none() {
            return;
        }
        if self.nal.is_some() || self.set_unit.is_some() {
            self.misuse("frame ended with a codec unit in progress; ending the unit");
        }
        if self.nal.is_some() {
            self.end_nal(sink);
        }
        if self.set_unit.is_some() {
            self.end_set_unit(sink);
        }

        // A frame of nothing but parameter sets (and perhaps an access unit
        // delimiter) still gets its insertion.
        self.insert_parameter_sets(sink);

        // Apply any parameter sets after the insertion point (or in a dropped
        // frame). Those passed through needn't be again; others which can't
        // be parsed are passed through at the next insertion point.
        let late_sets_delivered = std::mem::take(&mut self.late_sets_delivered);
        self.apply_new_sets(!late_sets_delivered);
        self.discarding_unit = false;
        self.dropping_frame = false;
        if self.held_kind != HeldKind::None {
            self.flush_held(true, sink);
        } else if self.flushed {
            let hdr = C::filler_header(self.frame_vcl_hdr);
            self.deliver(&[hdr.as_ref(), &FILLER_BODY], true, sink);
        }
        self.frame = None;
    }

    pub(crate) fn push_frame(
        &mut self,
        frame: VideoFrameInfo,
        framing: super::Framing,
        data: &[u8],
        sink: &mut impl PayloadSink,
    ) -> Result<(), Error> {
        let nals = super::NalUnits::new(framing, data).map_err(Error::invalid)?;

        // Validate everything first, so as to deliver nothing on error.
        for (_, body) in nals.clone() {
            let nal = &data[body];
            let Some(hdr) = Self::header(&[nal]) else {
                return Err(Error::invalid(format!(
                    "NAL {nal:02x?} is shorter than a NAL header"
                )));
            };
            if let Some(reason) = Self::invalid_header(hdr) {
                return Err(Error::invalid(format!(
                    "NAL header {hdr:02x?} has {reason}"
                )));
            }
        }
        self.start_frame(frame, sink);
        for (_, body) in nals {
            self.push_unit(Position::Complete, &[&data[body]], sink);
        }
        self.end_frame(sink);
        Ok(())
    }

    pub(crate) fn discontinuity(&mut self, sink: &mut impl PayloadSink) {
        self.frame = None;
        self.nal = None;
        self.discarding_unit = false;
        self.dropping_frame = false;

        // Parameter sets already supplied in full are kept, to apply at the
        // next insertion point.
        self.set_unit = None;
        self.insertion_pending = false;
        self.late_sets_delivered = false;

        // The lost data may have been depended on, so frames before the next
        // random access point may be undecodable.
        self.awaiting_rap = true;
        self.held.clear();
        self.held_kind = HeldKind::None;
        self.flushed = false;
        sink.discontinuity();
    }
}

/// Returns `hdr` with its F bit set, marking the NAL as damaged.
///
/// This is the H.264 `forbidden_zero_bit`, which RFC 6184 section 5.8 allows
/// setting on a NAL with bit errors or syntax violations; and the H.265
/// `forbidden_zero_bit`, which RFC 7798 section 1.1.4 allows setting on a NAL
/// missing its last fragment.
fn damaged<H: AsMut<[u8]>>(mut hdr: H) -> H {
    hdr.as_mut()[0] |= 0b1000_0000;
    hdr
}
