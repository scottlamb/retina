// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

#[cfg(test)]
use std::sync::Once;
use std::sync::OnceLock;

#[cfg(test)]
use bytes::Bytes;
use derive_more::Debug;
use pretty_hex::{HexConfig, PrettyHex as _};

#[cfg(test)]
static INIT_LOGGING: Once = Once::new();
static FINDER: OnceLock<memchr::memmem::Finder> = OnceLock::new();

pub const NONASCII_HEX_CONFIG: HexConfig = HexConfig {
    title: true,
    ascii: false,
    width: 16,
    group: 4,
    chunk: 1,
    max_bytes: usize::MAX,
    display_offset: 0,
};

#[allow(dead_code)]
#[derive(Debug)]
pub struct InvalidAvccFrame<'i> {
    reason: &'static str,

    #[debug("{:?}", data.hex_conf(NONASCII_HEX_CONFIG))]
    data: &'i [u8],
}

pub fn validate_avcc_frame(data: &[u8]) -> Result<(), InvalidAvccFrame<'_>> {
    let finder = FINDER.get_or_init(|| memchr::memmem::Finder::new(&[0, 0][..]));
    let mut remaining = data;
    while let Some((len, rest)) = remaining.split_first_chunk() {
        let len = u32::from_be_bytes(*len);
        let Some((nal, rest)) = rest.split_at_checked(len as usize) else {
            return Err(InvalidAvccFrame {
                reason: "ends mid-NAL",
                data,
            });
        };
        let body = match nal {
            [] => {
                return Err(InvalidAvccFrame {
                    reason: "NAL has zero length",
                    data,
                });
            }
            [_hdr, .., 0] => {
                return Err(InvalidAvccFrame {
                    reason: "NAL has trailing zero",
                    data,
                });
            }
            [_hdr, body @ ..] => body,
        };
        for i in finder.find_iter(body) {
            if body.get(i + 2).is_some_and(|b| [0, 1, 2].contains(b)) {
                return Err(InvalidAvccFrame {
                    reason: "NAL body has forbidden Annex B byte sequence",
                    data,
                });
            }
        }
        remaining = rest;
    }
    if !remaining.is_empty() {
        return Err(InvalidAvccFrame {
            reason: "frame ends mid-NAL length prefix",
            data,
        });
    }
    Ok(())
}

/// Opaque wrapper around `MarkBuf` for use in benchmarks and fuzz tests.
///
/// Provides a simple way to push payloads to a [`crate::codec::Depacketizer`]
/// without exposing the internal `MarkBuf` type.
pub struct DepacketizeBuf(crate::buf::MarkBuf);

impl DepacketizeBuf {
    /// Creates a new buffer with at least `capacity` bytes.
    pub fn new(capacity: usize) -> Self {
        Self(crate::buf::MarkBuf::new(capacity))
    }

    /// Pushes a payload to the depacketizer via the internal ring buffer.
    pub fn push(
        &mut self,
        d: &mut crate::codec::Depacketizer,
        meta: crate::rtp::PacketMeta,
        payload: &[u8],
    ) -> Result<(), String> {
        let pos = self.0.end();
        let len = payload.len();
        {
            let (s1, s2) = self.0.spare_capacity(len);
            if len <= s1.len() {
                s1[..len].copy_from_slice(payload);
            } else {
                s1.copy_from_slice(&payload[..s1.len()]);
                s2[..len - s1.len()].copy_from_slice(&payload[s1.len()..]);
            }
            self.0.advance_end(len);
        }
        self.0.advance_unparsed(self.0.end());
        d.push(&crate::buf::PacketRef::new(meta, &self.0, pos, len as u16))
    }
}

#[cfg(test)]
pub(crate) struct HexDebug(pub(crate) Vec<u8>);

#[cfg(test)]
impl std::cmp::PartialEq for HexDebug {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[cfg(test)]
impl std::cmp::Eq for HexDebug {}

#[cfg(test)]
impl std::fmt::Debug for HexDebug {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pretty_hex::pretty_hex_write(f, &self.0)
    }
}

#[cfg(test)]
macro_rules! assert_eq_hex {
    ($left:expr, $right:expr) => {{
        pretty_assertions::assert_eq!(
            $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref(&$left))),
            $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref(&$right))),
        );
    }};
}

#[cfg(test)]
macro_rules! assert_eq_hexes {
    ($left:expr, $right:expr) => {{
        let left = $left
            .iter()
            .map(|x| $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref(x))))
            .collect::<Vec<_>>();
        let right = $right
            .iter()
            .map(|x| $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref(x))))
            .collect::<Vec<_>>();
        pretty_assertions::assert_eq!(left, right);
    }};
}

#[cfg(test)]
pub(crate) use {assert_eq_hex, assert_eq_hexes};

#[cfg(test)]
pub(crate) fn init_logging() {
    use std::str::FromStr as _;
    INIT_LOGGING.call_once(|| {
        let h = mylog::Builder::new()
            .is_test(true)
            .format(
                ::std::env::var("RUST_FORMAT")
                    .map_err(|_| ())
                    .and_then(|s| mylog::Format::from_str(&s))
                    .unwrap_or(mylog::Format::Google),
            )
            .spec(::std::env::var("RUST_LOG").as_deref().unwrap_or("info"))
            .build();
        h.install().unwrap();
    })
}

#[cfg(test)]
pub(crate) fn response(mut raw: &'static [u8]) -> (crate::rtsp::msg::Response, Bytes) {
    let mut parser = crate::rtsp::parse::Parser::default();
    let (msg, body_slice) = parser.feed(&mut raw).unwrap().unwrap();
    assert!(raw.is_empty(), "not all bytes consumed");
    match msg {
        crate::rtsp::msg::Message::Response(r) => (r, Bytes::from_static(body_slice)),
        _ => panic!("unexpected message type"),
    }
}
