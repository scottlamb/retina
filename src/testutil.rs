// Copyright (C) 2022 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::str::FromStr;

use bytes::Bytes;

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
        rtsp_types::Message::Response(r) => r.map_body(|b| Bytes::from_static(b)),
        _ => panic!("unexpected message type"),
    }
}
