// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use bytes::Bytes;

pub(crate) fn response(raw: &'static [u8]) -> rtsp_types::Response<Bytes> {
    let (msg, len) = rtsp_types::Message::parse(raw).unwrap();
    assert_eq!(len, raw.len());
    match msg {
        rtsp_types::Message::Response(r) => r.map_body(|b| Bytes::from_static(b)),
        _ => panic!("unexpected message type"),
    }
}
