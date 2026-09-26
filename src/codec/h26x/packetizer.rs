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

use crate::Error;
use crate::codec::{
    FrameInfo, PacketizeOptions, ParameterSetInsertion, Payload, PayloadFormat, PayloadSink,
    Position, VideoParameters,
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
    fn parameters(sets: &[&[u8]]) -> Result<VideoParameters, String>;

    /// Returns a description of the stream, with parameter sets as in
    /// [`Codec::parameter_sets`].
    fn payload_format(parameters: &VideoParameters, sets: &[Bytes]) -> PayloadFormat;

    /// Returns the index into [`Codec::parameter_sets`] of a NAL with the
    /// given header, if it's a parameter set.
    fn parameter_set_index(hdr: Self::Header) -> Option<usize>;

    /// Returns why a NAL with the given header can't be packetized, if it
    /// can't.
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
}

/// Packetizes NAL units. See [`crate::codec::VideoPacketizer`].
///
/// To set the marker bit, the most recent payload is held back until the next
/// input shows it isn't the last of its frame. Held payloads are copied into
/// `held`; other payloads (all but the last fragment of each fragmented NAL)
/// are delivered with data referring directly to the input, except for a
/// remainder of less than one payload at the end of each input chunk.
#[derive(Debug)]
pub(crate) struct Packetizer<C: Codec> {
    max_payload_size: usize,
    aggregate: bool,
    parameter_set_insertion: ParameterSetInsertion,

    parameters: VideoParameters,

    /// The parameter sets within `parameters`, as in [`Codec::parameter_sets`].
    parameter_sets: Vec<Bytes>,

    /// True if parameters have changed since they were last inserted.
    parameters_changed: bool,

    frame: Option<FrameInfo>,

    /// True if no payload of `frame` has been delivered yet.
    frame_start_pending: bool,

    /// The NAL currently being supplied, if any.
    nal: Option<PacketizerNal<C::Header>>,

    /// A complete payload which hasn't been delivered yet, or empty.
    held: Vec<u8>,
    held_kind: HeldKind,

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
}

impl<C: Codec> Packetizer<C> {
    const HDR_LEN: usize = size_of::<C::Header>();
    const FU_HDR_LEN: usize = size_of::<C::FuHeader>();

    pub(crate) fn new(
        parameters: &VideoParameters,
        options: PacketizeOptions,
    ) -> Result<Self, Error> {
        let min = Self::FU_HDR_LEN + 1; // minimum size to make progress with fragments.
        if usize::from(options.max_payload_size) < min {
            return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                "max_payload_size must be at least {min}"
            ))));
        }
        let Some(parameter_sets) = C::parameter_sets(parameters) else {
            return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                "parameters are for a different codec: {}",
                parameters.rfc6381_codec()
            ))));
        };
        Ok(Self {
            max_payload_size: usize::from(options.max_payload_size),
            aggregate: options.aggregate,
            parameter_set_insertion: options.parameter_set_insertion,
            parameters: parameters.clone(),
            parameter_sets,
            parameters_changed: false,
            frame: None,
            frame_start_pending: false,
            nal: None,
            held: Vec::new(),
            held_kind: HeldKind::None,
            spare: Vec::new(),
            discarding_unit: false,
            seen_invalid_nal: false,
            seen_misuse: false,
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
            return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                "parameters are for a different codec: {}",
                parameters.rfc6381_codec()
            ))));
        };
        if parameter_sets != self.parameter_sets {
            self.parameter_sets = parameter_sets;
            self.parameters_changed = true;
        }
        self.parameters = parameters.clone();
        Ok(())
    }

    pub(crate) fn start_frame(&mut self, frame: FrameInfo, sink: &mut impl PayloadSink) {
        if self.frame.is_some() {
            self.end_frame(sink);
        }
        self.frame = Some(frame);
        self.frame_start_pending = true;
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
                self.push_unit(Position::Complete, &[&set], sink);
            }
        }
    }

    /// Notes misuse by the caller, logging only the first time.
    fn misuse(&mut self, what: &str) {
        if !self.seen_misuse {
            log::warn!("{what}; will not log about misuse again for this stream");
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
                C::invalid_header(hdr)
            };
            if let Some(reason) = invalid {
                if !self.seen_invalid_nal {
                    log::warn!(
                        "Discarding NAL with header {:02x?}: {reason}; \
                         will not log about this again for this stream",
                        &hdr.as_ref()[..filled],
                    );
                    self.seen_invalid_nal = true;
                }
                self.discarding_unit = !position.is_last();
                return;
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
            self.feed(d, sink);
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

    /// Ends the current NAL.
    fn end_nal(&mut self, sink: &mut impl PayloadSink) {
        let mut nal = self.nal.take().expect("end_nal with NAL in progress");
        self.end_nal_inner(&nal, sink);
        nal.buffered.clear();
        self.spare = nal.buffered;
    }

    fn end_nal_inner(&mut self, nal: &PacketizerNal<C::Header>, sink: &mut impl PayloadSink) {
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
        sink.payload(&Payload {
            timestamp: frame.timestamp,
            position: Position::new(first, mark),
            data,
            is_random_access_point: frame.is_random_access_point,
            is_disposable: frame.is_disposable,
        });
    }

    pub(crate) fn end_frame(&mut self, sink: &mut impl PayloadSink) {
        if self.frame.is_none() {
            return;
        }
        if self.nal.is_some() {
            self.misuse("frame ended with a codec unit in progress; ending the unit");
            self.end_nal(sink);
        }
        self.discarding_unit = false;
        self.flush_held(true, sink);
        self.frame = None;
    }

    pub(crate) fn push_frame(
        &mut self,
        frame: FrameInfo,
        framing: super::Framing,
        data: &[u8],
        sink: &mut impl PayloadSink,
    ) -> Result<(), Error> {
        let nals = crate::codec::packetize::split_nals(framing, data)
            .map_err(|e| wrap!(crate::error::ErrorInt::InvalidArgument(e)))?;
        let mut sets: Vec<Option<&[u8]>> = vec![None; C::PARAMETER_SETS];
        let mut is_set = Vec::with_capacity(nals.len());
        for nal in &nals {
            let Some(hdr_bytes) = nal.get(..Self::HDR_LEN) else {
                return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                    "NAL {nal:02x?} is shorter than a NAL header"
                ))));
            };
            let mut hdr = C::Header::default();
            hdr.as_mut().copy_from_slice(hdr_bytes);
            if hdr_bytes[0] & 0b1000_0000 != 0 {
                return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                    "NAL header {hdr_bytes:02x?} has F bit set"
                ))));
            }
            if let Some(reason) = C::invalid_header(hdr) {
                return Err(wrap!(crate::error::ErrorInt::InvalidArgument(format!(
                    "NAL header {hdr_bytes:02x?} has {reason}"
                ))));
            }
            let i = C::parameter_set_index(hdr);
            if let Some(i) = i {
                sets[i] = Some(*nal);
            }
            is_set.push(i.is_some());
        }
        if sets
            .iter()
            .zip(&self.parameter_sets)
            .any(|(new, old)| new.is_some_and(|n| n != &old[..]))
        {
            let merged: Vec<&[u8]> = sets
                .iter()
                .zip(&self.parameter_sets)
                .map(|(new, old)| new.unwrap_or(&old[..]))
                .collect();
            let p = C::parameters(&merged)
                .map_err(|e| wrap!(crate::error::ErrorInt::InvalidArgument(e)))?;
            self.set_parameters(&p)?;
        }
        self.start_frame(frame, sink);
        for (nal, is_set) in nals.into_iter().zip(is_set) {
            if !is_set {
                self.push_unit(Position::Complete, &[nal], sink);
            }
        }
        self.end_frame(sink);
        Ok(())
    }

    pub(crate) fn discontinuity(&mut self, sink: &mut impl PayloadSink) {
        self.frame = None;
        self.nal = None;
        self.discarding_unit = false;
        self.held.clear();
        self.held_kind = HeldKind::None;
        sink.discontinuity();
    }
}
