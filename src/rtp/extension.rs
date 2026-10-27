// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! RTP header extensions.
//!
//! These are public only with the `unstable-extensions` feature, which is
//! exempt from semver: it may change in any release.
//!
//! An RTP packet may carry one header extension block ([RFC 3550 section
//! 5.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.3.1)).
//! Nearly everyone fills that block with the general mechanism of [RFC
//! 8285](https://datatracker.ietf.org/doc/html/rfc8285): a list of elements,
//! each with a small local ID, which the SDP maps to a URI via `a=extmap`.
//! A few senders use a block of their own instead, such as the ONVIF
//! Streaming Specification's replay extension (profile `0xABAC`).
//!
//! Retina handles extensions at two levels:
//!
//! *   Raw: [`HeaderExtension`] is a packet's block, and
//!     [`HeaderExtension::elements`] iterates over its RFC 8285 elements.
//! *   Typed: each extension Retina understands is a type implementing
//!     [`Extension`], such as [`AbsCaptureTime`]. [`ExtensionIds`] holds the
//!     IDs a session negotiated for them, and [`Extensions`] holds their
//!     values. Values are independent of IDs, so they can pass from one
//!     session to another, as when a proxy depacketizes and repacketizes a
//!     stream.
//!
//! Values flow through Retina as follows:
//!
//! *   Receiving: [`crate::client`] reads the stream's `a=extmap` attributes
//!     into [`ExtensionIds`], and fills [`super::ReceivedPacketMeta::extensions`]
//!     with each packet's values. Depacketizers merge the values of each
//!     frame's packets, which are available as
//!     [`crate::codec::VideoFrameStart::extensions`] and
//!     [`crate::codec::VideoFrameEnd::extensions`].
//! *   Sending: [`crate::codec::VideoFrameInfo::with_extensions`] supplies a
//!     frame's values to a packetizer. The packetizer has its sink encode
//!     them once per frame ([`crate::codec::PayloadSink::serialize_extensions`]),
//!     leaves room for the encoded block in the frame's first payload, and
//!     attaches it there ([`crate::codec::Payload::encoded_extensions`]). A
//!     [`super::Sender`]'s sink encodes those values which have IDs via
//!     [`super::SenderOptions::extension_ids`], silently skipping the rest,
//!     and [`ExtensionIds::sdp_extmap`] describes them in the SDP.

// Without `unstable-extensions`, Retina carries extension values internally
// but nothing outside the crate can supply or read them.
#![cfg_attr(not(feature = "unstable-extensions"), allow(dead_code))]

use std::num::NonZeroU8;

use super::ParseError;
use crate::NtpTimestamp;

/// The RFC 8285 one-byte header profile.
const ONE_BYTE_PROFILE: u16 = 0xBEDE;

/// The RFC 8285 two-byte header profile, ignoring its low 4 "appbits".
const TWO_BYTE_PROFILE: u16 = 0x1000;

/// A packet's header extension block, as described in [RFC 3550 section
/// 5.3.1](https://datatracker.ietf.org/doc/html/rfc3550#section-5.3.1).
///
/// Obtain one from a packet via [`super::ValidatedPacket::extension`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct HeaderExtension<'a> {
    profile: u16,
    data: &'a [u8],
}

impl<'a> HeaderExtension<'a> {
    /// Creates a header extension with the given profile and data, the
    /// latter excluding the 4-byte profile and length header.
    #[inline]
    pub fn new(profile: u16, data: &'a [u8]) -> Self {
        Self { profile, data }
    }

    /// Returns the 16-bit "defined by profile" field.
    ///
    /// This is `0xBEDE` for RFC 8285 one-byte elements and `0x100X` for
    /// two-byte elements.
    #[inline]
    pub fn profile(&self) -> u16 {
        self.profile
    }

    /// Returns the extension's data, excluding the profile and length.
    #[inline]
    pub fn data(&self) -> &'a [u8] {
        self.data
    }

    /// Returns true if this block holds RFC 8285 elements.
    #[inline]
    pub fn is_rfc8285(&self) -> bool {
        self.profile == ONE_BYTE_PROFILE || (self.profile & 0xFFF0) == TWO_BYTE_PROFILE
    }

    /// Iterates over the block's RFC 8285 elements.
    ///
    /// Yields nothing if the block isn't in an RFC 8285 profile. Yields an
    /// error, then stops, if the block is malformed.
    #[inline]
    pub fn elements(&self) -> Elements<'a> {
        Elements {
            two_byte: (self.profile & 0xFFF0) == TWO_BYTE_PROFILE,
            data: if self.is_rfc8285() { self.data } else { &[] },
        }
    }

    /// Returns the first element with the given ID, if any.
    ///
    /// Malformed elements are ignored.
    pub fn get(&self, id: NonZeroU8) -> Option<&'a [u8]> {
        self.elements()
            .map_while(Result::ok)
            .find(|e| e.id == id)
            .map(|e| e.data)
    }
}

/// An RFC 8285 header extension element, as yielded by
/// [`HeaderExtension::elements`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Element<'a> {
    /// The element's local ID, which the SDP maps to a URI.
    pub id: NonZeroU8,

    /// The element's data.
    pub data: &'a [u8],
}

/// Iterator returned by [`HeaderExtension::elements`].
#[derive(Clone, Debug)]
pub struct Elements<'a> {
    two_byte: bool,
    data: &'a [u8],
}

impl<'a> Iterator for Elements<'a> {
    type Item = Result<Element<'a>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (&first, rest) = self.data.split_first()?;
            let (id, len, rest) = if self.two_byte {
                if first == 0 {
                    // Padding.
                    self.data = rest;
                    continue;
                }
                let Some((&len, rest)) = rest.split_first() else {
                    self.data = &[];
                    return Some(Err(ParseError("truncated two-byte extension element")));
                };
                (first, usize::from(len), rest)
            } else {
                let id = first >> 4;
                if id == 0 {
                    // Padding.
                    self.data = rest;
                    continue;
                }
                if id == 15 {
                    // RFC 8285 section 4.2: "processing of the entire
                    // extension MUST terminate at that point".
                    self.data = &[];
                    return None;
                }
                (id, usize::from(first & 0x0F) + 1, rest)
            };
            let Some((data, rest)) = rest.split_at_checked(len) else {
                self.data = &[];
                return Some(Err(ParseError("extension element extends beyond block")));
            };
            self.data = rest;
            return Some(Ok(Element {
                id: NonZeroU8::new(id).expect("zero IDs are padding"),
                data,
            }));
        }
    }
}

mod private {
    use std::num::NonZeroU8;

    /// Crate-internal parts of [`super::Extension`], which also seal it.
    pub trait Sealed: Sized {
        /// Returns the encoded length, from 1 to 255 bytes.
        fn encoded_len(&self) -> usize;

        /// Writes the encoded value to `out`, which is `encoded_len` bytes.
        fn encode(&self, out: &mut [u8]);

        fn value(values: &super::Extensions) -> &Option<Self>;
        fn value_mut(values: &mut super::Extensions) -> &mut Option<Self>;
        fn id(ids: &super::ExtensionIds) -> &Option<NonZeroU8>;
        fn id_mut(ids: &mut super::ExtensionIds) -> &mut Option<NonZeroU8>;
    }
}

/// A header extension Retina understands, usable as a key into
/// [`Extensions`] and [`ExtensionIds`].
///
/// This is sealed: Retina stores the values of each known extension inline,
/// without allocation, so callers can't add their own. Extensions Retina
/// doesn't know remain accessible via [`HeaderExtension::elements`].
pub trait Extension: Copy + std::fmt::Debug + private::Sealed {
    /// The URI identifying this extension in SDP `a=extmap` attributes.
    const URI: &'static str;

    /// Parses an element's data.
    fn parse(data: &[u8]) -> Result<Self, ParseError>;
}

/// The absolute capture time extension, as described in
/// [`http://www.webrtc.org/experiments/rtp-hdrext/abs-capture-time`](https://webrtc.googlesource.com/src/+/refs/heads/main/docs/native-code/rtp-hdrext/abs-capture-time/README.md).
///
/// This states the wall clock time at which the packet's media was captured,
/// as a sender report would but per packet, so a receiver can measure
/// end-to-end latency or align streams from different senders. Unlike a
/// sender report's mapping, it survives relays and mixers unchanged.
///
/// Senders typically attach it to a frame's first packet, and not
/// necessarily to every frame (libwebrtc sends it about once a second, or
/// when the mapping from RTP timestamp changes unexpectedly). A receiver can
/// extrapolate to other frames via their RTP timestamps.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AbsCaptureTime {
    /// The time the first sample of the media was captured, on the capture
    /// system's wall clock.
    pub capture_time: NtpTimestamp,

    /// The capture system's NTP clock minus the sender's NTP clock, in
    /// seconds as a signed Q32.32 fixed-point number, if known.
    ///
    /// The sender is whoever generated the RTCP sender reports for the
    /// stream. Adding this offset to the receiver's estimate of the sender's
    /// clock offset gives the capture system's offset from the receiver's
    /// clock.
    pub estimated_capture_clock_offset: Option<i64>,
}

impl AbsCaptureTime {
    /// Returns an extension with the given capture time and no estimated
    /// capture clock offset.
    #[inline]
    pub fn new(capture_time: NtpTimestamp) -> Self {
        Self {
            capture_time,
            estimated_capture_clock_offset: None,
        }
    }
}

impl private::Sealed for AbsCaptureTime {
    fn encoded_len(&self) -> usize {
        if self.estimated_capture_clock_offset.is_some() {
            16
        } else {
            8
        }
    }

    fn encode(&self, out: &mut [u8]) {
        out[..8].copy_from_slice(&self.capture_time.0.to_be_bytes());
        if let Some(o) = self.estimated_capture_clock_offset {
            out[8..16].copy_from_slice(&o.to_be_bytes());
        }
    }

    fn value(values: &Extensions) -> &Option<Self> {
        &values.abs_capture_time
    }

    fn value_mut(values: &mut Extensions) -> &mut Option<Self> {
        &mut values.abs_capture_time
    }

    fn id(ids: &ExtensionIds) -> &Option<NonZeroU8> {
        &ids.abs_capture_time
    }

    fn id_mut(ids: &mut ExtensionIds) -> &mut Option<NonZeroU8> {
        &mut ids.abs_capture_time
    }
}

impl Extension for AbsCaptureTime {
    const URI: &'static str = "http://www.webrtc.org/experiments/rtp-hdrext/abs-capture-time";

    fn parse(data: &[u8]) -> Result<Self, ParseError> {
        let (capture_time, offset) = match data.len() {
            8 => (data, None),
            16 => {
                let (t, o) = data.split_at(8);
                (t, Some(i64::from_be_bytes(o.try_into().unwrap())))
            }
            _ => return Err(ParseError("abs-capture-time must be 8 or 16 bytes")),
        };
        Ok(Self {
            capture_time: NtpTimestamp(u64::from_be_bytes(capture_time.try_into().unwrap())),
            estimated_capture_clock_offset: offset,
        })
    }
}

/// Calls `$f!(Type, field)` for each known extension.
macro_rules! for_each_extension {
    ($f:ident) => {
        $f!(AbsCaptureTime, abs_capture_time);
    };
}

/// The values of the [`Extension`]s known for a packet or frame.
///
/// This is a typed map, keyed by the extension's type, in the spirit of
/// [`http::Extensions`](https://docs.rs/http/latest/http/struct.Extensions.html).
/// It's `Copy` and doesn't allocate.
///
/// ```
/// # #[cfg(feature = "unstable-extensions")]
/// # {
/// use retina::rtp::{AbsCaptureTime, Extensions};
/// let mut e = Extensions::default();
/// assert!(e.get::<AbsCaptureTime>().is_none());
/// e.insert(AbsCaptureTime::new(retina::NtpTimestamp(1 << 32)));
/// assert_eq!(e.get::<AbsCaptureTime>().unwrap().capture_time.0, 1 << 32);
/// # }
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct Extensions {
    abs_capture_time: Option<AbsCaptureTime>,
}

impl Extensions {
    /// Returns the value of extension `E`, if present.
    #[inline]
    pub fn get<E: Extension>(&self) -> Option<&E> {
        E::value(self).as_ref()
    }

    /// Sets the value of extension `E`, returning the previous value.
    #[inline]
    pub fn insert<E: Extension>(&mut self, value: E) -> Option<E> {
        E::value_mut(self).replace(value)
    }

    /// Removes the value of extension `E`, returning it.
    #[inline]
    pub fn remove<E: Extension>(&mut self) -> Option<E> {
        E::value_mut(self).take()
    }

    /// Returns `self` with the value of extension `E` set.
    #[inline]
    pub fn with<E: Extension>(mut self, value: E) -> Self {
        self.insert(value);
        self
    }

    /// Returns true if no values are present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        *self == Self::default()
    }

    /// Fills in values from `other` which are absent in `self`.
    ///
    /// Depacketizers use this to merge the values of a frame's packets, so
    /// the first packet with each extension wins.
    pub fn fill_from(&mut self, other: &Extensions) {
        macro_rules! fill {
            ($t:ty, $field:ident) => {
                if self.$field.is_none() {
                    self.$field = other.$field;
                }
            };
        }
        for_each_extension!(fill);
    }
}

/// The local IDs a session uses for the [`Extension`]s Retina knows, as
/// negotiated via SDP `a=extmap` attributes ([RFC 8285 section
/// 5](https://datatracker.ietf.org/doc/html/rfc8285#section-5)).
///
/// It's empty by default: no extensions are read or written.
///
/// ```
/// # #[cfg(feature = "unstable-extensions")]
/// # {
/// use retina::rtp::{AbsCaptureTime, ExtensionIds};
/// let mut ids = ExtensionIds::default();
/// ids.parse_extmap("3 http://www.webrtc.org/experiments/rtp-hdrext/abs-capture-time").unwrap();
/// assert_eq!(ids.get::<AbsCaptureTime>().map(|i| i.get()), Some(3));
/// # }
/// ```
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ExtensionIds {
    abs_capture_time: Option<NonZeroU8>,
}

const NUM_EXTENSIONS: usize = {
    let mut n = 0;
    macro_rules! count {
        ($t:ty, $field:ident) => {
            n += 1;
        };
    }
    for_each_extension!(count);
    n
};

impl ExtensionIds {
    /// Returns the ID of extension `E`, if it's in use.
    #[inline]
    pub fn get<E: Extension>(&self) -> Option<NonZeroU8> {
        *E::id(self)
    }

    /// Returns `self` with extension `E` assigned ID `id`.
    ///
    /// IDs 1–14 can be written with RFC 8285's one-byte elements; IDs
    /// 15–255 require two-byte elements, which receivers needn't support.
    /// Prefer 1–14.
    #[inline]
    pub fn with<E: Extension>(mut self, id: NonZeroU8) -> Self {
        *E::id_mut(&mut self) = Some(id);
        self
    }

    /// Returns true if no extensions are in use.
    #[inline]
    pub fn is_empty(&self) -> bool {
        *self == Self::default()
    }

    /// Notes the value of an SDP `a=extmap` attribute (the part after
    /// `extmap:`), e.g. `1 http://www.webrtc.org/experiments/rtp-hdrext/abs-capture-time`.
    ///
    /// Returns `Ok(true)` if the URI is a known extension, which is now
    /// assigned that ID, or `Ok(false)` if it's not known. Returns an error if
    /// the attribute is malformed.
    pub fn parse_extmap(&mut self, value: &str) -> Result<bool, String> {
        let mut parts = value.split_ascii_whitespace();
        let (Some(id), Some(uri)) = (parts.next(), parts.next()) else {
            return Err(format!("malformed extmap {value:?}"));
        };
        // Strip any direction, as in `1/sendonly`.
        let id = id.split_once('/').map_or(id, |(id, _)| id);
        let id = id
            .parse::<NonZeroU8>()
            .map_err(|_| format!("bad extmap id in {value:?}"))?;
        macro_rules! check {
            ($t:ty, $field:ident) => {
                if uri == <$t as Extension>::URI {
                    self.$field = Some(id);
                    return Ok(true);
                }
            };
        }
        for_each_extension!(check);
        Ok(false)
    }

    /// Returns `(id, uri)` for each extension in use, for writing SDP
    /// `a=extmap:{id} {uri}` attributes.
    pub fn sdp_extmap(&self) -> impl Iterator<Item = (NonZeroU8, &'static str)> + use<> {
        let mut out = smallvec::SmallVec::<[_; NUM_EXTENSIONS]>::new();
        macro_rules! push {
            ($t:ty, $field:ident) => {
                if let Some(id) = self.$field {
                    out.push((id, <$t as Extension>::URI));
                }
            };
        }
        for_each_extension!(push);
        out.into_iter()
    }

    /// Reads the values of known extensions from a packet's header extension.
    ///
    /// Elements with unknown IDs are ignored, as are malformed elements and
    /// values. Retina logs these at debug level.
    pub fn read(&self, ext: &HeaderExtension<'_>) -> Extensions {
        let mut out = Extensions::default();
        if self.is_empty() {
            return out;
        }
        for e in ext.elements() {
            let e = match e {
                Ok(e) => e,
                Err(err) => {
                    tracing::debug!(%err, "malformed RTP header extension");
                    break;
                }
            };
            macro_rules! read {
                ($t:ty, $field:ident) => {
                    if self.$field == Some(e.id) && out.$field.is_none() {
                        match <$t as Extension>::parse(e.data) {
                            Ok(v) => out.$field = Some(v),
                            Err(err) => tracing::debug!(%err, "bad RTP header extension value"),
                        }
                    }
                };
            }
            for_each_extension!(read);
        }
        out
    }

    /// Encodes `values` with these IDs as a header extension block,
    /// including its 4-byte profile and length header, replacing the
    /// contents of `out`.
    ///
    /// Values without an ID are skipped. The block's length is a multiple
    /// of 4, or 0 if there's nothing to write.
    #[cfg_attr(not(feature = "unstable-send"), allow(dead_code))]
    pub(crate) fn encode(&self, values: &Extensions, out: &mut Vec<u8>) {
        out.clear();
        // Choose one-byte elements if every ID and length allows.
        let mut any = false;
        let mut one_byte = true;
        macro_rules! check {
            ($t:ty, $field:ident) => {
                if let (Some(id), Some(v)) = (self.$field, &values.$field) {
                    any = true;
                    let len = private::Sealed::encoded_len(v);
                    one_byte &= id.get() <= 14 && (1..=16).contains(&len);
                }
            };
        }
        for_each_extension!(check);
        if !any {
            return;
        }
        let profile = if one_byte {
            ONE_BYTE_PROFILE
        } else {
            TWO_BYTE_PROFILE
        };
        out.extend_from_slice(&profile.to_be_bytes());
        out.extend_from_slice(&[0, 0]); // length, filled in below.
        macro_rules! write {
            ($t:ty, $field:ident) => {
                if let (Some(id), Some(v)) = (self.$field, &values.$field) {
                    let len = private::Sealed::encoded_len(v);
                    if one_byte {
                        out.push((id.get() << 4) | (len - 1) as u8);
                    } else {
                        out.extend_from_slice(&[id.get(), len as u8]);
                    }
                    let pos = out.len();
                    out.resize(pos + len, 0);
                    private::Sealed::encode(v, &mut out[pos..]);
                }
            };
        }
        for_each_extension!(write);
        out.resize((out.len() + 3) & !3, 0); // padding.
        let words = u16::try_from((out.len() - 4) / 4).expect("block fits in u16 words");
        out[2..4].copy_from_slice(&words.to_be_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(i: u8) -> NonZeroU8 {
        NonZeroU8::new(i).unwrap()
    }

    #[test]
    fn one_byte_elements() {
        // RFC 8285 section 4.2's example: ID 1 with 1 byte, padding, ID 2
        // with 2 bytes, then ID 15, which ends processing.
        let data = [0x10, 0xaa, 0x00, 0x21, 0xbb, 0xcc, 0xf0, 0xdd];
        let ext = HeaderExtension::new(0xBEDE, &data);
        let elements: Vec<_> = ext.elements().collect::<Result<_, _>>().unwrap();
        assert_eq!(
            elements,
            [
                Element {
                    id: id(1),
                    data: &[0xaa]
                },
                Element {
                    id: id(2),
                    data: &[0xbb, 0xcc]
                },
            ]
        );
        assert_eq!(ext.get(id(2)), Some(&[0xbb, 0xcc][..]));
    }

    #[test]
    fn two_byte_elements() {
        let data = [0x00, 0x20, 0x00, 0x30, 0x01, 0xaa, 0x00, 0x00];
        let ext = HeaderExtension::new(0x1003, &data);
        let elements: Vec<_> = ext.elements().collect::<Result<_, _>>().unwrap();
        assert_eq!(
            elements,
            [
                Element {
                    id: id(32),
                    data: &[]
                },
                Element {
                    id: id(48),
                    data: &[0xaa]
                },
            ]
        );
    }

    #[test]
    fn truncated() {
        let ext = HeaderExtension::new(0xBEDE, &[0x13, 0xaa]);
        assert!(ext.elements().next().unwrap().is_err());
        let ext = HeaderExtension::new(0x1000, &[0x01]);
        assert!(ext.elements().next().unwrap().is_err());
    }

    #[test]
    fn other_profile() {
        // ONVIF's replay extension isn't RFC 8285.
        let ext = HeaderExtension::new(0xABAC, &[0x10, 0xaa, 0, 0]);
        assert!(!ext.is_rfc8285());
        assert_eq!(ext.elements().count(), 0);
    }

    #[test]
    fn round_trip() {
        for (ext_id, offset, expected_profile, expected_len) in [
            (3, None, ONE_BYTE_PROFILE, 4 + 12),
            (3, Some(-(1 << 32)), ONE_BYTE_PROFILE, 4 + 20),
            (200, Some(5), TWO_BYTE_PROFILE, 4 + 20),
        ] {
            let ids = ExtensionIds::default().with::<AbsCaptureTime>(id(ext_id));
            let v = AbsCaptureTime {
                capture_time: NtpTimestamp(0x0102_0304_0506_0708),
                estimated_capture_clock_offset: offset,
            };
            let values = Extensions::default().with(v);
            let mut buf = vec![0xff; 3]; // replaced, not appended to.
            ids.encode(&values, &mut buf);
            let len = buf.len();
            assert_eq!(len, expected_len);
            let profile = u16::from_be_bytes([buf[0], buf[1]]);
            assert_eq!(profile, expected_profile);
            assert_eq!(
                usize::from(u16::from_be_bytes([buf[2], buf[3]])) * 4 + 4,
                len
            );
            let ext = HeaderExtension::new(profile, &buf[4..len]);
            assert_eq!(ids.read(&ext), values);
        }
    }

    #[test]
    fn encode_nothing() {
        let mut buf = vec![0xff];
        let values = Extensions::default().with(AbsCaptureTime::new(NtpTimestamp(1)));
        ExtensionIds::default().encode(&values, &mut buf);
        assert!(buf.is_empty());
        let ids = ExtensionIds::default().with::<AbsCaptureTime>(id(1));
        buf.push(0xff);
        ids.encode(&Extensions::default(), &mut buf);
        assert!(buf.is_empty());
    }

    #[test]
    fn parse_extmap() {
        let mut ids = ExtensionIds::default();
        assert_eq!(
            ids.parse_extmap(
                "2/recvonly http://www.webrtc.org/experiments/rtp-hdrext/abs-capture-time"
            ),
            Ok(true)
        );
        assert_eq!(ids.get::<AbsCaptureTime>(), Some(id(2)));
        assert_eq!(
            ids.parse_extmap("1 urn:ietf:params:rtp-hdrext:toffset"),
            Ok(false)
        );
        assert!(ids.parse_extmap("x urn:foo").is_err());
        assert!(ids.parse_extmap("0 urn:foo").is_err());
        assert!(ids.parse_extmap("1").is_err());
        assert_eq!(
            ids.sdp_extmap().collect::<Vec<_>>(),
            [(id(2), AbsCaptureTime::URI)]
        );
    }

    #[test]
    fn malformed_value_ignored() {
        let ids = ExtensionIds::default().with::<AbsCaptureTime>(id(1));
        let data = [0x13, 1, 2, 3, 4]; // ID 1, 4 bytes: too short.
        let ext = HeaderExtension::new(ONE_BYTE_PROFILE, &data);
        assert!(ids.read(&ext).is_empty());
    }
}
