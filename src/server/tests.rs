// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;
use crate::testutil::init_logging;

fn addr() -> SocketAddr {
    "127.0.0.1:554".parse().unwrap()
}

fn core() -> ConnectionCore<&'static str> {
    ConnectionCore::new(addr(), addr(), ServerOptions::default())
}

/// Parses all responses written by `core`.
fn responses<T>(core: &mut ConnectionCore<T>) -> Vec<(msg::Response, String)> {
    let (a, b) = core.transmit_buf();
    let bytes = [a, b].concat();
    core.advance_transmit(bytes.len());
    let mut parser = crate::rtsp::parse::Parser::default();
    let mut input = &bytes[..];
    let mut out = Vec::new();
    while let Some((m, body)) = parser.feed(&mut input).unwrap() {
        let msg::Message::Response(r) = m else {
            panic!("expected response, got {m:?}")
        };
        out.push((r, String::from_utf8(body.to_vec()).unwrap()));
    }
    assert!(input.is_empty());
    out
}

fn one_response<T>(core: &mut ConnectionCore<T>) -> (msg::Response, String) {
    let mut r = responses(core);
    assert_eq!(r.len(), 1, "{r:#?}");
    r.pop().unwrap()
}

fn header<'a>(r: &'a msg::Response, name: &str) -> &'a str {
    r.headers
        .get(name)
        .unwrap_or_else(|| panic!("no {name} in {r:#?}"))
}

#[test]
fn options_and_errors() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    c.read_buf().extend(
        b"OPTIONS rtsp://h/ RTSP/1.0\r\nCSeq: 1\r\n\r\n\
          PLAY rtsp://h/ RTSP/1.0\r\nCSeq: 2\r\nSession: 1234\r\n\r\n\
          SETUP rtsp://h/a RTSP/1.0\r\nCSeq: 3\r\nTransport: RTP/AVP;unicast;client_port=5000-5001\r\n\r\n\
          ANNOUNCE rtsp://h/ RTSP/1.0\r\nCSeq: 4\r\n\r\n\
          DESCRIBE rtsp://h/ RTSP/1.0\r\nCSeq: 5\r\nRequire: funky\r\n\r\n",
    );
    assert!(c.poll_event(now).is_none());
    let r = responses(&mut c);
    let statuses: Vec<_> = r
        .iter()
        .map(|(r, _)| (header(r, "CSeq").to_owned(), r.status_code.as_u16()))
        .collect();
    assert_eq!(
        statuses,
        [
            ("1".into(), 200),
            ("2".into(), 454),
            ("3".into(), 461),
            ("4".into(), 501),
            ("5".into(), 551),
        ]
    );
    assert!(header(&r[0].0, "Public").contains("DESCRIBE"));
    assert_eq!(header(&r[4].0, "Unsupported"), "funky");
}

#[test]
fn full_session() {
    init_logging();
    let mut c = core();
    let now = Instant::now();

    // DESCRIBE.
    c.read_buf()
        .extend(b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 1\r\n\r\n");
    let Some(Ok(Event::Describe(d))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(d.url().unwrap().as_str(), "rtsp://h/cam");
    c.respond_describe(d, Ok("v=0\r\n"));
    let (r, body) = one_response(&mut c);
    assert_eq!(r.status_code, StatusCode::OK);
    assert_eq!(header(&r, "Content-Base"), "rtsp://h/cam/");
    assert_eq!(header(&r, "Content-Type"), "application/sdp");
    assert_eq!(body, "v=0\r\n");

    // SETUP two streams; the second asks for channels in use.
    c.read_buf().extend(
        b"SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 2\r\n\
          Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n",
    );
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(s.channel(), 0);
    assert!(s.is_new_session());
    let id = s.session_id();
    assert_eq!(c.respond_setup(s, Ok(("video", 0x1234))), Ok(id));
    let (r, _) = one_response(&mut c);
    assert_eq!(header(&r, "Session"), format!("{id};timeout=60"));
    assert_eq!(
        header(&r, "Transport"),
        "RTP/AVP/TCP;unicast;interleaved=0-1;ssrc=00001234"
    );
    c.read_buf().extend(
        format!(
            "SETUP rtsp://h/cam/trackID=1 RTSP/1.0\r\nCSeq: 3\r\nSession: {id}\r\n\
             Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n"
        )
        .as_bytes(),
    );
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(s.channel(), 2);
    assert!(!s.is_new_session());
    assert_eq!(s.session_id(), id);
    assert_eq!(c.respond_setup(s, Ok(("audio", 0x5678))), Ok(id));
    let (r, _) = one_response(&mut c);
    assert!(header(&r, "Transport").contains("interleaved=2-3"));

    // PLAY.
    c.read_buf().extend(
        format!("PLAY rtsp://h/cam/ RTSP/1.0\r\nCSeq: 4\r\nSession: {id}\r\n\r\n").as_bytes(),
    );
    let Some(Ok(Event::Play(p))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(p.session_id(), id);
    let data: Vec<_> = c.streams(id).unwrap().iter().map(|s| s.data).collect();
    assert_eq!(data, ["video", "audio"]);
    c.respond_play(
        p,
        Ok(&[
            RtpInfo {
                seq: Some(1),
                rtptime: Some(2),
            },
            RtpInfo {
                seq: Some(3),
                rtptime: None,
            },
        ]),
    )
    .unwrap();
    let (r, _) = one_response(&mut c);
    assert_eq!(
        header(&r, "RTP-Info"),
        "url=rtsp://h/cam/trackID=0;seq=1;rtptime=2,url=rtsp://h/cam/trackID=1;seq=3"
    );

    // Keepalives: a request with the session, and RTCP.
    let later = now + Duration::from_secs(50);
    c.read_buf().extend(
        format!("GET_PARAMETER rtsp://h/cam/ RTSP/1.0\r\nCSeq: 5\r\nSession: {id}\r\n\r\n")
            .as_bytes(),
    );
    assert!(c.poll_event(later).is_none());
    assert_eq!(one_response(&mut c).0.status_code, StatusCode::OK);
    assert_eq!(c.poll_timeout(), Some(later + Duration::from_secs(60)));
    let later = later + Duration::from_secs(50);
    c.read_buf().extend(b"$\x03\x00\x02rr");
    assert!(c.poll_event(later).is_none());
    assert_eq!(c.poll_timeout(), Some(later + Duration::from_secs(60)));

    // TEARDOWN.
    c.read_buf().extend(
        format!("TEARDOWN rtsp://h/cam/ RTSP/1.0\r\nCSeq: 6\r\nSession: {id}\r\n\r\n").as_bytes(),
    );
    let Some(Ok(Event::Teardown(t))) = c.poll_event(later) else {
        panic!()
    };
    assert_eq!(t.session_id(), id);
    assert!(responses(&mut c).is_empty());
    let streams = c.respond_teardown(t).unwrap();
    assert_eq!(streams.len(), 2);
    assert_eq!(one_response(&mut c).0.status_code, StatusCode::OK);
    assert!(c.poll_event(later).is_none());
    assert_eq!(c.poll_timeout(), None);
}

#[test]
fn timeout() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    c.read_buf().extend(
        b"SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 1\r\n\
          Transport: RTP/AVP/TCP;unicast\r\n\r\n",
    );
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(s.channel(), 0);
    let id = c.respond_setup(s, Ok(("video", 0))).unwrap();
    assert!(c.poll_event(now).is_none());
    let deadline = c.poll_timeout().unwrap();
    c.handle_timeout(deadline - Duration::from_millis(1));
    assert!(c.poll_event(now).is_none());
    c.handle_timeout(deadline);
    let Some(Ok(Event::SessionTimedOut(closed))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(closed.id, id);
}

#[test]
fn dropped_request_gets_500() {
    init_logging();
    let mut c = core();
    c.read_buf()
        .extend(b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 1\r\n\r\n");
    let Some(Ok(Event::Describe(d))) = c.poll_event(Instant::now()) else {
        panic!()
    };
    drop(d);
    assert!(responses(&mut c).is_empty());
    assert!(c.poll_event(Instant::now()).is_none());
    assert_eq!(one_response(&mut c).0.status_code.as_u16(), 500);
}

/// Retina's client understands the SDP.
#[test]
fn sdp_round_trip() {
    init_logging();
    let video = crate::codec::PayloadFormat::new("video", "H264", 90_000).with_fmtp(
        "packetization-mode=1;profile-level-id=42C01E;\
         sprop-parameter-sets=Z0LAHtkDxWhAAAADAEAAAAwDxYuS,aMuMsg==",
    );
    let audio = crate::codec::PayloadFormat::new("audio", "PCMU", 8_000)
        .with_channels(std::num::NonZeroU16::new(1).unwrap());
    let body = sdp(
        "test",
        &[
            SdpMedia::new(&video, 96, "trackID=0"),
            SdpMedia::new(&audio, 0, "trackID=1"),
        ],
    );
    let response = msg::Response {
        status_code: StatusCode::OK,
        reason_phrase: "OK".into(),
        headers: [
            (HeaderName::CONTENT_TYPE, hv("application/sdp")),
            (HeaderName::CONTENT_BASE, hv("rtsp://h/cam/")),
        ]
        .into(),
    };
    let p = crate::client::parse::parse_describe(
        Url::parse("rtsp://h/cam").unwrap(),
        &response,
        &bytes::Bytes::from(body),
        false,
    )
    .unwrap();
    assert_eq!(p.control.as_str(), "rtsp://h/cam/");
    assert_eq!(p.streams.len(), 2);
    let v = &p.streams[0];
    assert_eq!(
        (v.media(), v.encoding_name(), v.rtp_payload_type()),
        ("video", "h264", 96)
    );
    assert_eq!(v.control().unwrap().as_str(), "rtsp://h/cam/trackID=0");
    assert_eq!(v.parameters().is_some(), cfg!(feature = "h264"));
    let a = &p.streams[1];
    assert_eq!(
        (
            a.media(),
            a.encoding_name(),
            a.clock_rate_hz(),
            a.channels()
        ),
        ("audio", "pcmu", 8_000, std::num::NonZeroU16::new(1))
    );
    assert_eq!(a.control().unwrap().as_str(), "rtsp://h/cam/trackID=1");
}

/// Sets up a one-stream session on channels 0-1, returning its id.
fn setup<T>(c: &mut ConnectionCore<T>, data: T, now: Instant) -> SessionId {
    c.read_buf().extend(
        b"SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 1\r\n\
          Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n",
    );
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    let id = c.respond_setup(s, Ok((data, 0))).unwrap();
    assert!(c.poll_event(now).is_none());
    assert_eq!(one_response(c).0.status_code, StatusCode::OK);
    id
}

fn statuses<T>(c: &mut ConnectionCore<T>) -> Vec<(String, u16)> {
    responses(c)
        .iter()
        .map(|(r, _)| (header(r, "CSeq").to_owned(), r.status_code.as_u16()))
        .collect()
}

/// While a request is outstanding, the core keeps processing interleaved
/// data, but holds later requests so responses stay in order.
#[test]
fn pipelined_while_outstanding() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    setup(&mut c, "video", now);
    c.read_buf().extend(
        b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 2\r\n\r\n\
          $\x01\x00\x02rr\
          OPTIONS rtsp://h/ RTSP/1.0\r\nCSeq: 3\r\n\r\n\
          $\x01\x00\x02rr",
    );
    let Some(Ok(Event::Describe(d))) = c.poll_event(now) else {
        panic!()
    };
    let later = now + Duration::from_secs(10);
    assert!(c.poll_event(later).is_none());
    assert!(responses(&mut c).is_empty());
    assert_eq!(c.poll_timeout(), Some(later + Duration::from_secs(60)));
    assert!(c.wants_read());

    // Answering releases the held OPTIONS, then the data after it.
    c.respond_describe(d, Ok("v=0\r\n"));
    let even_later = later + Duration::from_secs(10);
    assert!(c.poll_event(even_later).is_none());
    assert_eq!(statuses(&mut c), [("2".into(), 200), ("3".into(), 200)]);
    assert_eq!(c.poll_timeout(), Some(even_later + Duration::from_secs(60)));
}

/// A dropped request is answered with a 500, after which held requests
/// proceed.
#[test]
fn dropped_request_releases_held() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    c.read_buf().extend(
        b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 1\r\n\r\n\
          OPTIONS rtsp://h/ RTSP/1.0\r\nCSeq: 2\r\n\r\n",
    );
    let Some(Ok(Event::Describe(d))) = c.poll_event(now) else {
        panic!()
    };
    assert!(c.poll_event(now).is_none());
    drop(d);
    assert!(c.poll_event(now).is_none());
    assert_eq!(statuses(&mut c), [("1".into(), 500), ("2".into(), 200)]);
}

/// A session with an outstanding `PLAY` doesn't time out; its timeout
/// restarts from the first `poll_event` after the answer.
#[test]
fn outstanding_play_suspends_timeout() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    let id = setup(&mut c, "video", now);
    c.read_buf().extend(
        format!("PLAY rtsp://h/cam/ RTSP/1.0\r\nCSeq: 2\r\nSession: {id}\r\n\r\n").as_bytes(),
    );
    let Some(Ok(Event::Play(p))) = c.poll_event(now) else {
        panic!()
    };
    let later = now + Duration::from_secs(120);
    c.handle_timeout(later);
    assert!(c.poll_event(later).is_none());
    assert!(c.streams(id).is_some());
    c.streams_mut(id).unwrap()[0].data = "taken";
    c.respond_play(p, Ok(&[RtpInfo::default()])).unwrap();
    assert_eq!(one_response(&mut c).0.status_code, StatusCode::OK);
    assert!(c.poll_event(later).is_none());
    assert_eq!(c.poll_timeout(), Some(later + Duration::from_secs(60)));
    assert_eq!(c.streams(id).unwrap()[0].data, "taken");
}

/// A client pipelining lots behind an outstanding request is eventually
/// asked to wait.
#[test]
fn wants_read_bounded_while_held() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    c.read_buf().extend(
        b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 1\r\n\r\n\
          OPTIONS rtsp://h/ RTSP/1.0\r\nCSeq: 2\r\n\r\n",
    );
    let Some(Ok(Event::Describe(d))) = c.poll_event(now) else {
        panic!()
    };
    assert!(c.poll_event(now).is_none());
    assert!(c.wants_read());
    c.read_buf().extend(&[b'$'; MAX_UNPARSED_WHILE_HELD]);
    assert!(c.poll_event(now).is_none());
    assert!(!c.wants_read());
    c.respond_describe(d, Err(StatusCode::NOT_FOUND));
    let _ = c.poll_event(now);
    assert!(c.wants_read());
}

#[test]
#[should_panic(expected = "outstanding request")]
fn foreign_pending_panics() {
    let mut a = core();
    let mut b = core();
    a.read_buf()
        .extend(b"DESCRIBE rtsp://h/cam RTSP/1.0\r\nCSeq: 1\r\n\r\n");
    let Some(Ok(Event::Describe(d))) = a.poll_event(Instant::now()) else {
        panic!()
    };
    b.respond_describe(d, Ok(""));
}

/// Until `TEARDOWN` is answered, the session's channels stay allocated, so
/// a later `SETUP` can't reuse them while the application may still be
/// sending.
#[test]
fn teardown_keeps_channels_until_answered() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    let id = setup(&mut c, "video", now);
    c.read_buf().extend(
        format!(
            "TEARDOWN rtsp://h/cam/ RTSP/1.0\r\nCSeq: 2\r\nSession: {id}\r\n\r\n\
             SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 3\r\n\
             Transport: RTP/AVP/TCP;unicast;interleaved=0-1\r\n\r\n"
        )
        .as_bytes(),
    );
    let Some(Ok(Event::Teardown(t))) = c.poll_event(now) else {
        panic!()
    };
    assert!(c.poll_event(now).is_none());
    assert_eq!(c.streams(id).unwrap()[0].channel, 0);
    let streams = c.respond_teardown(t).unwrap();
    assert_eq!(streams[0].data, "video");
    assert!(c.streams(id).is_none());
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    assert_eq!(s.channel(), 0);
    assert_eq!(statuses(&mut c), [("2".into(), 200)]);
}

#[test]
fn no_session_timeout() {
    init_logging();
    let mut c = ConnectionCore::new(
        addr(),
        addr(),
        ServerOptions::default().session_timeout(None),
    );
    let now = Instant::now();
    c.read_buf().extend(
        b"SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 1\r\n\
          Transport: RTP/AVP/TCP;unicast\r\n\r\n",
    );
    let Some(Ok(Event::Setup(s))) = c.poll_event(now) else {
        panic!()
    };
    let id = c.respond_setup(s, Ok(("video", 0))).unwrap();
    assert!(c.poll_event(now).is_none());
    assert_eq!(header(&one_response(&mut c).0, "Session"), id.to_string());
    assert_eq!(c.poll_timeout(), None);
    c.handle_timeout(now + Duration::from_secs(3600));
    assert!(c.poll_event(now).is_none());
    assert!(c.streams(id).is_some());
}

/// `into_sessions` returns every session, including timed-out ones not yet
/// returned as events.
#[test]
fn into_sessions() {
    init_logging();
    let mut c = core();
    let now = Instant::now();
    let a = setup(&mut c, "a", now);
    c.read_buf().extend(
        b"SETUP rtsp://h/cam/trackID=0 RTSP/1.0\r\nCSeq: 2\r\n\
          Transport: RTP/AVP/TCP;unicast\r\n\r\n",
    );
    let later = now + Duration::from_secs(30);
    let Some(Ok(Event::Setup(s))) = c.poll_event(later) else {
        panic!()
    };
    let b = c.respond_setup(s, Ok(("b", 0))).unwrap();
    assert!(c.poll_event(later).is_none());
    c.handle_timeout(now + Duration::from_secs(60));
    let mut sessions: Vec<_> = c
        .into_sessions()
        .map(|s| (s.id, s.streams[0].data))
        .collect();
    sessions.sort_by_key(|&(_, d)| d);
    assert_eq!(sessions, [(a, "a"), (b, "b")]);
}
