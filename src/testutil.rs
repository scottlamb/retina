// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::str::FromStr;

use bytes::Bytes;

pub(crate) struct HexDebug(pub(crate) Vec<u8>);

impl std::cmp::PartialEq for HexDebug {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl std::cmp::Eq for HexDebug {}

impl std::fmt::Debug for HexDebug {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pretty_hex::pretty_hex_write(f, &self.0)
    }
}

macro_rules! assert_eq_hex {
    ($left:expr, $right:expr) => {{
        pretty_assertions::assert_eq!(
            $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref($left))),
            $crate::testutil::HexDebug(Vec::from(AsRef::<[u8]>::as_ref($right))),
        );
    }};
}

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

pub(crate) use {assert_eq_hex, assert_eq_hexes};

pub(crate) fn init_logging() {
    let h = mylog::Builder::new()
        .set_format(
            ::std::env::var("MOONFIRE_FORMAT")
                .map_err(|_| ())
                .and_then(|s| mylog::Format::from_str(&s))
                .unwrap_or(mylog::Format::Google),
        )
        .set_spec(::std::env::var("MOONFIRE_LOG").as_deref().unwrap_or("info"))
        .build();
    let _ = h.install();
}

pub(crate) fn response(raw: &'static [u8]) -> rtsp_types::Response<Bytes> {
    let (msg, len) = rtsp_types::Message::parse(raw).unwrap();
    assert_eq!(len, raw.len());
    match msg {
        rtsp_types::Message::Response(r) => r.map_body(Bytes::from_static),
        _ => panic!("unexpected message type"),
    }
}
