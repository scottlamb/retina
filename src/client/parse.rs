// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use bytes::Bytes;
use log::debug;
use pretty_hex::PrettyHex;
use sdp_types::Media;
use std::{net::IpAddr, num::NonZeroU16};
use url::Url;

use super::{Presentation, Stream};

/// A static payload type in the [RTP parameters
/// registry](https://www.iana.org/assignments/rtp-parameters/rtp-parameters.xhtml#rtp-parameters-1).
#[derive(Debug)]
struct StaticPayloadType {
    encoding: &'static str,
    media: &'static str,
    clock_rate: u32,
    channels: Option<NonZeroU16>,
}

/// All registered static payload types.
/// The registry is officially closed, so this list should never change.
#[rustfmt::skip]
static STATIC_PAYLOAD_TYPES: [Option<StaticPayloadType>; 35] = [
    /* 0 */ Some(StaticPayloadType {
        encoding: "pcmu",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 1 */ None, // reserved
    /* 2 */ None, // reserved
    /* 3 */ Some(StaticPayloadType {
        encoding: "gsm",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 4 */ Some(StaticPayloadType {
        encoding: "g723",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 5 */ Some(StaticPayloadType {
        encoding: "dvi4",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 6 */ Some(StaticPayloadType {
        encoding: "dvi4",
        media: "audio",
        clock_rate: 16_000,
        channels: NonZeroU16::new(1),
    }),
    /* 7 */ Some(StaticPayloadType {
        encoding: "lpc",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 8 */ Some(StaticPayloadType {
        encoding: "pcma",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 9 */ Some(StaticPayloadType {
        encoding: "g722",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 10 */ Some(StaticPayloadType {
        encoding: "l16",
        media: "audio",
        clock_rate: 441_000,
        channels: NonZeroU16::new(2),
    }),
    /* 11 */ Some(StaticPayloadType {
        encoding: "l16",
        media: "audio",
        clock_rate: 441_000,
        channels: NonZeroU16::new(1),
    }),
    /* 12 */ Some(StaticPayloadType {
        encoding: "qcelp",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 13 */ Some(StaticPayloadType {
        encoding: "cn",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 14 */ Some(StaticPayloadType {
        encoding: "mpa",
        media: "audio",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 15 */ Some(StaticPayloadType {
        encoding: "g728",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 16 */ Some(StaticPayloadType {
        encoding: "dvi4",
        media: "audio",
        clock_rate: 11_025,
        channels: NonZeroU16::new(1),
    }),
    /* 17 */ Some(StaticPayloadType {
        encoding: "dvi4",
        media: "audio",
        clock_rate: 22_050,
        channels: NonZeroU16::new(1),
    }),
    /* 18 */ Some(StaticPayloadType {
        encoding: "g729",
        media: "audio",
        clock_rate: 8_000,
        channels: NonZeroU16::new(1),
    }),
    /* 19 */ None, // reserved
    /* 20 */ None, // unassigned
    /* 21 */ None, // unassigned
    /* 22 */ None, // unassigned
    /* 23 */ None, // unassigned
    /* 24 */ None, // unassigned
    /* 25 */ Some(StaticPayloadType {
        encoding: "celb",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 26 */ Some(StaticPayloadType {
        encoding: "jpeg",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 27 */ None, // unassigned
    /* 28 */ Some(StaticPayloadType {
        encoding: "nv",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 29 */ None, // unassigned
    /* 30 */ None, // unassigned
    /* 31 */ Some(StaticPayloadType {
        encoding: "h261",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 32 */ Some(StaticPayloadType {
        encoding: "mpv",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 33 */ Some(StaticPayloadType {
        encoding: "mp2t",
        // The RTP parameters registry says type AV (audio and video).
        // The MIME registration says the media type is "video".
        // https://datatracker.ietf.org/doc/html/rfc3555#section-4.2.9
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
    /* 34 */ Some(StaticPayloadType {
        encoding: "h263",
        media: "video",
        clock_rate: 90_000,
        channels: None,
    }),
];

/// Joins a control URL to a base URL in a non-RFC-compliant but common way.
/// This matches what live555 and ffmpeg do.
///
/// See discussion at [#9](https://github.com/scottlamb/retina/issues/9).
fn join_control(base_url: &Url, control: &str) -> Result<Url, String> {
    if control == "*" {
        return Ok(base_url.clone());
    }
    if let Ok(absolute_url) = Url::parse(control) {
        return Ok(absolute_url);
    }

    Url::parse(&format!(
        "{}{}{}",
        base_url.as_str(),
        if base_url.as_str().ends_with('/') {
            ""
        } else {
            "/"
        },
        control
    ))
    .map_err(|e| {
        format!(
            "unable to join base url {} with control url {:?}: {}",
            base_url, control, e
        )
    })
}

/// Returns the `CSeq` from an RTSP response as a `u32`, or `None` if missing/unparseable.
pub(crate) fn get_cseq(response: &rtsp_types::Response<Bytes>) -> Option<u32> {
    response
        .header(&rtsp_types::headers::CSEQ)
        .and_then(|cseq| u32::from_str_radix(cseq.as_str(), 10).ok())
}

/// Parses a [MediaDescription] to a [Stream].
/// On failure, returns an error which is expected to be supplemented with
/// the [MediaDescription] debug string and packed into a `RtspResponseError`.
fn parse_media(base_url: &Url, media_description: &Media) -> Result<Stream, String> {
    let media = media_description.media.clone();

    // https://tools.ietf.org/html/rfc8866#section-5.14 says "If the <proto>
    // sub-field is "RTP/AVP" or "RTP/SAVP" the <fmt> sub-fields contain RTP
    // payload type numbers."
    // https://www.iana.org/assignments/sdp-parameters/sdp-parameters.xhtml#sdp-parameters-2
    // shows several other variants, such as "TCP/RTP/AVP". Looking for a "RTP" component
    // seems appropriate.
    if !media_description.proto.starts_with("RTP/") && !media_description.proto.contains("/RTP/") {
        return Err("Expected RTP-based proto".into());
    }

    // RFC 8866 continues: "When a list of payload type numbers is given,
    // this implies that all of these payload formats MAY be used in the
    // session, but the first of these formats SHOULD be used as the default
    // format for the session." Just use the first until we find a stream
    // where this isn't the right thing to do.
    let rtp_payload_type_str = media_description
        .fmt
        .split_ascii_whitespace()
        .next()
        .unwrap();
    let rtp_payload_type = u8::from_str_radix(rtp_payload_type_str, 10)
        .map_err(|_| format!("invalid RTP payload type {:?}", rtp_payload_type_str))?;
    if (rtp_payload_type & 0x80) != 0 {
        return Err(format!("invalid RTP payload type {}", rtp_payload_type));
    }

    // Capture interesting attributes.
    // RFC 8866: "For dynamic payload type assignments, the "a=rtpmap:"
    // attribute (see Section 6.6) SHOULD be used to map from an RTP payload
    // type number to a media encoding name that identifies the payload
    // format. The "a=fmtp:" attribute MAY be used to specify format
    // parameters (see Section 6.15)."
    let mut rtpmap = None;
    let mut fmtp = None;
    let mut control = None;
    for a in &media_description.attributes {
        if a.attribute == "rtpmap" {
            let v = a
                .value
                .as_ref()
                .ok_or_else(|| "rtpmap attribute with no value".to_string())?;
            // https://tools.ietf.org/html/rfc8866#section-6.6
            // rtpmap-value = payload-type SP encoding-name
            //   "/" clock-rate [ "/" encoding-params ]
            // payload-type = zero-based-integer
            // encoding-name = token
            // clock-rate = integer
            // encoding-params = channels
            // channels = integer
            let (rtpmap_payload_type, v) = v
                .split_once(' ')
                .ok_or_else(|| "invalid rtmap attribute".to_string())?;
            if rtpmap_payload_type == rtp_payload_type_str {
                rtpmap = Some(v);
            }
        } else if a.attribute == "fmtp" {
            // Similarly starts with payload-type SP.
            let v = a
                .value
                .as_ref()
                .ok_or_else(|| "fmtp attribute with no value".to_string())?;
            let (fmtp_payload_type, v) = v
                .split_once(' ')
                .ok_or_else(|| "invalid fmtp attribute".to_string())?;
            if fmtp_payload_type == rtp_payload_type_str {
                fmtp = Some(v);
            }
        } else if a.attribute == "control" {
            control = a
                .value
                .as_deref()
                .map(|c| join_control(base_url, c))
                .transpose()?;
        }
    }

    let encoding_name;
    let clock_rate;
    let channels;
    match rtpmap {
        Some(rtpmap) => {
            let (e, rtpmap) = rtpmap
                .split_once('/')
                .ok_or_else(|| "invalid rtpmap attribute".to_string())?;
            encoding_name = e;
            let (clock_rate_str, channels_str) = match rtpmap.find('/') {
                None => (rtpmap, None),
                Some(i) => (&rtpmap[..i], Some(&rtpmap[i + 1..])),
            };
            clock_rate = u32::from_str_radix(clock_rate_str, 10)
                .map_err(|_| "bad clockrate in rtpmap".to_string())?;
            channels = channels_str
                .map(|c| {
                    u16::from_str_radix(c, 10)
                        .ok()
                        .and_then(NonZeroU16::new)
                        .ok_or_else(|| format!("Invalid channels specification {:?}", c))
                })
                .transpose()?;
        }
        None => {
            let type_ = STATIC_PAYLOAD_TYPES
                .get(usize::from(rtp_payload_type))
                .and_then(Option::as_ref)
                .ok_or_else(|| {
                    format!(
                        "Expected rtpmap parameter or assigned static payload type (got {})",
                        rtp_payload_type
                    )
                })?;
            encoding_name = type_.encoding;
            clock_rate = type_.clock_rate;
            channels = type_.channels;
            if type_.media != media {
                return Err(format!(
                    "SDP media type {} must match RTP payload type {:#?}",
                    &media, type_
                ));
            }
        }
    }

    let encoding_name = encoding_name.to_ascii_lowercase();
    let depacketizer =
        crate::codec::Depacketizer::new(&media, &encoding_name, clock_rate, channels, fmtp);

    Ok(Stream {
        media,
        encoding_name,
        clock_rate,
        rtp_payload_type,
        depacketizer,
        control,
        sockets: None,
        channels,
        state: super::StreamState::Uninit,
    })
}

/// Parses a successful RTSP `DESCRIBE` response into a [Presentation].
/// On error, returns a string which is expected to be packed into an `RtspProtocolError`.
pub(crate) fn parse_describe(
    request_url: Url,
    response: &rtsp_types::Response<Bytes>,
) -> Result<Presentation, String> {
    if !matches!(response.header(&rtsp_types::headers::CONTENT_TYPE), Some(v) if v.as_str() == "application/sdp")
    {
        return Err(format!(
            "Describe response not of expected application/sdp content type: {:#?}",
            &response
        ));
    }

    let sdp = sdp_types::Session::parse(&response.body()[..]).map_err(|e| {
        format!(
            "Unable to parse SDP: {}\n\n{:#?}",
            e,
            response.body().hex_dump()
        )
    })?;

    // https://tools.ietf.org/html/rfc2326#appendix-C.1.1
    let base_url = response
        .header(&rtsp_types::headers::CONTENT_BASE)
        .map(|v| (rtsp_types::headers::CONTENT_BASE, v))
        .or_else(|| {
            response
                .header(&rtsp_types::headers::CONTENT_LOCATION)
                .map(|v| (rtsp_types::headers::CONTENT_LOCATION, v))
        })
        .map(|(h, v)| Url::parse(v.as_str()).map_err(|e| format!("bad {} {:?}: {}", h, v, e)))
        .unwrap_or(Ok(request_url.clone()))?;

    let mut control = None;
    let mut tool = None;
    for a in &sdp.attributes {
        if a.attribute == "control" {
            control = a
                .value
                .as_deref()
                .map(|c| join_control(&base_url, c))
                .transpose()?;
            break;
        } else if a.attribute == "tool" {
            tool = a.value.as_deref().map(Into::into);
        }
    }
    let control = control.unwrap_or(request_url);

    let streams = sdp
        .medias
        .iter()
        .enumerate()
        .map(|(i, m)| {
            parse_media(&base_url, &m)
                .map_err(|e| format!("Unable to parse stream {}: {}\n\n{:#?}", i, &e, &m))
        })
        .collect::<Result<Vec<Stream>, String>>()?;

    let accept_dynamic_rate =
        matches!(response.header(&crate::X_ACCEPT_DYNAMIC_RATE), Some(h) if h.as_str() == "1");

    Ok(Presentation {
        streams,
        base_url,
        control,
        accept_dynamic_rate,
        tool,
    })
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct SessionHeader {
    pub(crate) id: Box<str>,
    pub(crate) timeout_sec: u32,
}

pub(crate) struct SetupResponse {
    pub(crate) session: SessionHeader,
    pub(crate) ssrc: Option<u32>,
    pub(crate) channel_id: Option<u8>,
    pub(crate) source: Option<IpAddr>,
    pub(crate) server_port: Option<(u16, u16)>,
}

/// Parses a `SETUP` response.
/// `session_id` is checked for assignment or reassignment.
/// Returns an assigned interleaved channel id (implying the next channel id
/// is also assigned) or errors.
pub(crate) fn parse_setup(response: &rtsp_types::Response<Bytes>) -> Result<SetupResponse, String> {
    // https://datatracker.ietf.org/doc/html/rfc2326#section-12.37
    let session = response
        .header(&rtsp_types::headers::SESSION)
        .ok_or_else(|| "Missing Session header".to_string())?;
    let session = match session.as_str().split_once(';') {
        None => SessionHeader {
            id: session.as_str().into(),
            timeout_sec: 60, // default
        },
        Some((id, timeout_str)) => {
            if let Some(v) = timeout_str.trim().strip_prefix("timeout=") {
                let timeout_sec =
                    u32::from_str_radix(v, 10).map_err(|_| format!("Unparseable timeout {}", v))?;
                SessionHeader {
                    id: id.into(),
                    timeout_sec,
                }
            } else {
                return Err(format!("Unparseable Session header {:?}", session.as_str()));
            }
        }
    };
    let transport = response
        .header(&rtsp_types::headers::TRANSPORT)
        .ok_or_else(|| "Missing Transport header".to_string())?;
    let mut channel_id = None;
    let mut ssrc = None;
    let mut source = None;
    let mut server_port = None;
    for part in transport.as_str().split(';') {
        if let Some(v) = part.strip_prefix("ssrc=") {
            let v = u32::from_str_radix(v, 16).map_err(|_| format!("Unparseable ssrc {}", v))?;
            ssrc = Some(v);
            break;
        } else if let Some(interleaved) = part.strip_prefix("interleaved=") {
            let mut channels = interleaved.splitn(2, '-');
            let n = channels.next().expect("splitn returns at least one part");
            let n = u8::from_str_radix(n, 10).map_err(|_| format!("bad channel number {}", n))?;
            if let Some(m) = channels.next() {
                let m = u8::from_str_radix(m, 10)
                    .map_err(|_| format!("bad second channel number {}", m))?;
                if n.checked_add(1) != Some(m) {
                    format!("Expected adjacent channels; got {}-{}", n, m);
                }
            }
            channel_id = Some(n);
        } else if let Some(s) = part.strip_prefix("source=") {
            source = Some(
                s.parse()
                    .map_err(|_| format!("Transport header has unparseable source {:?}", s))?,
            );
        } else if let Some(s) = part.strip_prefix("server_port=") {
            let mut ports = s.splitn(2, '-');
            let n = ports.next().expect("splitn returns at least one part");
            let n = u16::from_str_radix(n, 10)
                .map_err(|_| format!("bad port in Transport: {}", transport.as_str()))?;
            if let Some(m) = ports.next() {
                let m = u16::from_str_radix(m, 10).map_err(|_| format!("bad second port {}", m))?;
                server_port = Some((n, m))
            } else {
                // TODO: this is allowed by RFC 2326's grammar, but I'm not sure
                // what it means. Does it use the same port for both RTP and
                // RTCP, or is it implied the second is one more than the first?
                return Err("Transport header specifies a single server_port".to_owned());
            }
        }
    }
    Ok(SetupResponse {
        session,
        ssrc,
        channel_id,
        source,
        server_port,
    })
}

/// Parses a `PLAY` response. The error should always be packed into a `RtspProtocolError`.
pub(crate) fn parse_play(
    response: &rtsp_types::Response<Bytes>,
    presentation: &mut Presentation,
) -> Result<(), String> {
    // https://tools.ietf.org/html/rfc2326#section-12.33
    let rtp_info = match response.header(&rtsp_types::headers::RTP_INFO) {
        Some(rtsp_info) => rtsp_info,
        None => return Ok(()),
    };
    for s in rtp_info.as_str().split(',') {
        let s = s.trim();
        let mut parts = s.split(';');
        let url = parts
            .next()
            .expect("split always returns at least one part")
            .strip_prefix("url=")
            .ok_or_else(|| "RTP-Info missing stream URL".to_string())?;
        let url = join_control(&presentation.base_url, url)?;
        let stream;
        if presentation.streams.len() == 1 {
            // The server is allowed to not specify a stream control URL for
            // single-stream presentations. Additionally, some buggy
            // cameras (eg the GW Security GW4089IP) use an incorrect URL.
            // When there is a single stream in the presentation, there's no
            // ambiguity. Be "forgiving", just as RFC 2326 section 14.3 asks
            // servers to be forgiving of clients with single-stream
            // containers.
            // https://datatracker.ietf.org/doc/html/rfc2326#section-14.3
            stream = Some(&mut presentation.streams[0]);
        } else {
            stream = presentation
                .streams
                .iter_mut()
                .find(|s| matches!(&s.control, Some(u) if u == &url));
        }
        let stream = match stream {
            Some(s) => s,
            None => {
                log::warn!("RTP-Info contains unknown stream {}", url);
                continue;
            }
        };
        let state = match &mut stream.state {
            super::StreamState::Uninit => {
                // This appears to happen for Reolink devices when we did not send a SETUP request
                // for all streams. It also happens in some of other the tests
                // here simply because I didn't include all the SETUP steps.
                debug!(
                    "PLAY response described stream {} in Uninit state",
                    stream.control.as_ref().unwrap_or(&presentation.control)
                );
                continue;
            }
            super::StreamState::Init(init) => init,
            super::StreamState::Playing { .. } => unreachable!(),
        };
        for part in parts {
            let (key, value) = part
                .split_once('=')
                .ok_or_else(|| "RTP-Info param has no =".to_string())?;
            match key {
                "seq" => {
                    let seq = u16::from_str_radix(value, 10)
                        .map_err(|_| format!("bad seq {:?}", value))?;
                    state.initial_seq = Some(seq);
                }
                "rtptime" => {
                    let rtptime = u32::from_str_radix(value, 10)
                        .map_err(|_| format!("bad rtptime {:?}", value))?;
                    state.initial_rtptime = Some(rtptime);
                }
                "ssrc" => {
                    let ssrc = u32::from_str_radix(value, 16)
                        .map_err(|_| format!("Unparseable ssrc {}", value))?;
                    state.ssrc = Some(ssrc);
                }
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroU16;

    use bytes::Bytes;
    use url::Url;

    use crate::{client::StreamStateInit, codec::Parameters};

    use super::super::StreamState;
    use super::SessionHeader;
    use crate::testutil::response;

    fn parse_describe(
        raw_url: &str,
        raw_response: &'static [u8],
    ) -> Result<super::Presentation, String> {
        let url = Url::parse(raw_url).unwrap();
        super::parse_describe(url, &response(raw_response))
    }

    #[test]
    fn anvpiz_sdp() {
        let url = Url::parse("rtsp://127.0.0.1/").unwrap();
        let response =
            rtsp_types::Response::builder(rtsp_types::Version::V1_0, rtsp_types::StatusCode::Ok)
                .header(rtsp_types::headers::CONTENT_TYPE, "application/sdp")
                .build(Bytes::from_static(include_bytes!(
                    "testdata/anpviz_sdp.txt"
                )));
        super::parse_describe(url, &response).unwrap();
    }

    #[test]
    fn geovision_sdp() {
        let url = Url::parse("rtsp://127.0.0.1/").unwrap();
        let response =
            rtsp_types::Response::builder(rtsp_types::Version::V1_0, rtsp_types::StatusCode::Ok)
                .header(rtsp_types::headers::CONTENT_TYPE, "application/sdp")
                .build(Bytes::from_static(include_bytes!(
                    "testdata/geovision_sdp.txt"
                )));
        super::parse_describe(url, &response).unwrap();
    }

    #[test]
    fn dahua_h264_aac_onvif() {
        // DESCRIBE.
        let prefix =
            "rtsp://192.168.5.111:554/cam/realmonitor?channel=1&subtype=1&unicast=true&proto=Onvif";
        let mut p = parse_describe(
            prefix,
            include_bytes!("testdata/dahua_describe_h264_aac_onvif.txt"),
        )
        .unwrap();
        assert_eq!(p.control.as_str(), &(prefix.to_string() + "/"));
        assert!(p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 3);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=0")
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.64001E");
                assert_eq!(v.pixel_dimensions(), (704, 480));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), Some((2, 30)));
            }
            _ => panic!(),
        }

        // .mp4 audio stream.
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=1")
        );
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "mpeg4-generic");
        assert_eq!(p.streams[1].rtp_payload_type, 97);
        assert_eq!(p.streams[1].clock_rate, 48_000);
        match p.streams[1].parameters() {
            Some(Parameters::Audio(_)) => {}
            _ => panic!(),
        }

        // ONVIF parameters stream.
        assert_eq!(
            p.streams[2].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=4")
        );
        assert_eq!(p.streams[2].media, "application");
        assert_eq!(p.streams[2].encoding_name, "vnd.onvif.metadata");
        assert_eq!(p.streams[2].rtp_payload_type, 107);
        assert_eq!(p.streams[2].clock_rate, 90_000);
        assert!(matches!(
            p.streams[2].parameters(),
            Some(Parameters::Message(_))
        ));

        // SETUP.
        let setup_response = response(include_bytes!("testdata/dahua_setup.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "634214675641".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, Some(0x30a98ee7));
        p.streams[0].state = StreamState::Init(StreamStateInit {
            ssrc: setup_response.ssrc,
            initial_seq: None,
            initial_rtptime: None,
        });

        // PLAY.
        super::parse_play(&response(include_bytes!("testdata/dahua_play.txt")), &mut p).unwrap();
        match &p.streams[0].state {
            StreamState::Init(s) => {
                assert_eq!(s.initial_seq, Some(47121));
                assert_eq!(s.initial_rtptime, Some(3475222385));
            }
            _ => panic!(),
        };
        // The other streams don't get filled in because they're in state Uninit.
    }

    #[test]
    fn dahua_h265_pcma() {
        let p = parse_describe(
            "rtsp://192.168.5.111:554/cam/realmonitor?channel=1&subtype=2",
            include_bytes!("testdata/dahua_describe_h265_pcma.txt"),
        )
        .unwrap();

        // Abridged test; similar to the other Dahua test.
        assert_eq!(p.streams.len(), 2);
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h265");
        assert_eq!(p.streams[0].rtp_payload_type, 98);
        assert!(p.streams[0].parameters().is_none());
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "pcma");
        assert_eq!(p.streams[1].rtp_payload_type, 8);
        match p.streams[1].parameters().unwrap() {
            Parameters::Audio(_) => {}
            _ => panic!(),
        };
    }

    #[test]
    fn hikvision() {
        // DESCRIBE.
        let prefix = "rtsp://192.168.5.106:554/Streaming/Channels/101";
        let mut p = parse_describe(
            &(prefix.to_string() + "?transportmode=unicast&Profile=Profile_1"),
            include_bytes!("testdata/hikvision_describe.txt"),
        )
        .unwrap();
        assert_eq!(
            p.base_url.as_str(),
            "rtsp://192.168.5.106:554/Streaming/Channels/101/"
        );
        assert!(!p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 2);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=1?transportmode=unicast&profile=Profile_1")
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.4D0029");
                assert_eq!(v.pixel_dimensions(), (1920, 1080));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), Some((2_000, 60_000)));
            }
            _ => panic!(),
        }

        // ONVIF parameters stream.
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=3?transportmode=unicast&profile=Profile_1")
        );
        assert_eq!(p.streams[1].media, "application");
        assert_eq!(p.streams[1].encoding_name, "vnd.onvif.metadata");
        assert_eq!(p.streams[1].rtp_payload_type, 107);
        assert_eq!(p.streams[1].clock_rate, 90_000);
        assert!(matches!(
            p.streams[1].parameters(),
            Some(Parameters::Message(_))
        ));

        // SETUP.
        let setup_response = response(include_bytes!("testdata/hikvision_setup.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "708345999".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, Some(0x4cacc3d1));
        p.streams[0].state = StreamState::Init(StreamStateInit {
            ssrc: setup_response.ssrc,
            initial_seq: None,
            initial_rtptime: None,
        });

        // PLAY.
        super::parse_play(
            &response(include_bytes!("testdata/hikvision_play.txt")),
            &mut p,
        )
        .unwrap();
        match p.streams[0].state {
            StreamState::Init(state) => {
                assert_eq!(state.initial_seq, Some(24104));
                assert_eq!(state.initial_rtptime, Some(1270711678));
            }
            _ => panic!(),
        }
        // The other stream isn't filled in because it's in state Uninit.
    }

    #[test]
    fn reolink() {
        // DESCRIBE.
        let mut p = parse_describe(
            "rtsp://192.168.5.206:554/h264Preview_01_main",
            include_bytes!("testdata/reolink_describe.txt"),
        )
        .unwrap();
        let base = "rtsp://192.168.5.206/h264Preview_01_main/";
        assert_eq!(p.control.as_str(), base);
        assert!(!p.accept_dynamic_rate);
        assert_eq!(
            p.tool.as_deref(),
            Some("LIVE555 Streaming Media v2013.04.08")
        );

        assert_eq!(p.streams.len(), 2);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(base.to_string() + "trackID=1")
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.640033");
                assert_eq!(v.pixel_dimensions(), (2560, 1440));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), None);
            }
            _ => panic!(),
        };

        // audio stream
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(base.to_string() + "trackID=2")
        );
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "mpeg4-generic");
        assert_eq!(p.streams[1].rtp_payload_type, 97);
        assert_eq!(p.streams[1].clock_rate, 16_000);
        match p.streams[1].parameters() {
            Some(Parameters::Audio(_)) => {}
            _ => panic!(),
        }

        // SETUP.
        let setup_response = response(include_bytes!("testdata/reolink_setup.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "F8F8E425".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, None);
        p.streams[0].state = StreamState::Init(StreamStateInit::default());
        p.streams[1].state = StreamState::Init(StreamStateInit::default());

        // PLAY.
        super::parse_play(
            &response(include_bytes!("testdata/reolink_play.txt")),
            &mut p,
        )
        .unwrap();
        match p.streams[0].state {
            StreamState::Init(state) => {
                assert_eq!(state.initial_seq, Some(16852));
                assert_eq!(state.initial_rtptime, Some(1070938629));
            }
            _ => panic!(),
        };
        match p.streams[1].state {
            StreamState::Init(state) => {
                assert_eq!(state.initial_rtptime, Some(3075976528));
                assert_eq!(state.ssrc, Some(0x9fc9fff8));
            }
            _ => panic!(),
        };
    }

    #[test]
    fn bunny() {
        // This is a public test server for Wowza Streaming Engine.
        // https://www.wowza.com/html/mobile.html

        // DESCRIBE.
        let prefix = "rtsp://wowzaec2demo.streamlock.net/vod/mp4:BigBuckBunny_115k.mov";
        let mut p = parse_describe(prefix, include_bytes!("testdata/bunny_describe.txt")).unwrap();
        assert_eq!(p.control.as_str(), &(prefix.to_string() + "/"));
        assert!(!p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 2);

        // audio stream
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=1")
        );
        assert_eq!(p.streams[0].media, "audio");
        assert_eq!(p.streams[0].encoding_name, "mpeg4-generic");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 12_000);
        assert_eq!(p.streams[0].channels, NonZeroU16::new(2));
        match p.streams[0].parameters() {
            Some(Parameters::Audio(_)) => {}
            _ => panic!(),
        }

        // H.264 video stream.
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/trackID=2")
        );
        assert_eq!(p.streams[1].media, "video");
        assert_eq!(p.streams[1].encoding_name, "h264");
        assert_eq!(p.streams[1].rtp_payload_type, 97);
        assert_eq!(p.streams[1].clock_rate, 90_000);
        match p.streams[1].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.42C01E");
                assert_eq!(v.pixel_dimensions(), (240, 160));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), Some((2, 48)));
            }
            _ => panic!(),
        }

        // SETUP.
        let setup_response = response(include_bytes!("testdata/bunny_setup.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "1642021126".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, None);
        p.streams[0].state = StreamState::Init(StreamStateInit::default());
        p.streams[1].state = StreamState::Init(StreamStateInit::default());

        // PLAY.
        super::parse_play(&response(include_bytes!("testdata/bunny_play.txt")), &mut p).unwrap();
        match p.streams[1].state {
            StreamState::Init(state) => {
                assert_eq!(state.initial_rtptime, Some(0));
                assert_eq!(state.initial_seq, Some(1));
                assert_eq!(state.ssrc, None);
            }
            _ => panic!(),
        };
    }

    #[test]
    fn foscam() {
        // DESCRIBE.
        let prefix = "rtsp://192.168.5.107:65534/videoMain";
        let p = parse_describe(prefix, include_bytes!("testdata/foscam_describe.txt")).unwrap();
        assert_eq!(p.control.as_str(), &(prefix.to_string() + "/"));
        assert!(!p.accept_dynamic_rate);
        assert_eq!(
            p.tool.as_deref(),
            Some("LIVE555 Streaming Media v2014.02.10")
        );

        assert_eq!(p.streams.len(), 2);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/track1")
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.4D001F");
                assert_eq!(v.pixel_dimensions(), (1280, 720));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), None);
            }
            _ => panic!(),
        }

        // audio stream
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/track2")
        );
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "pcmu");
        assert_eq!(p.streams[1].rtp_payload_type, 0);
        assert_eq!(p.streams[1].clock_rate, 8_000);
        assert_eq!(p.streams[1].channels, NonZeroU16::new(1));
        match p.streams[1].parameters().unwrap() {
            Parameters::Audio(_) => {}
            _ => panic!(),
        };
    }

    #[test]
    fn vstarcam() {
        // DESCRIBE.
        let prefix = "rtsp://192.168.1.198:10554/tcp/av0_0";
        let p = parse_describe(prefix, include_bytes!("testdata/vstarcam_describe.txt")).unwrap();
        assert_eq!(p.control.as_str(), &(prefix.to_string()));

        assert!(!p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 2);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/track0")
        );

        assert_eq!(p.streams[0].media, "video");

        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);

        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.4D002A");
                assert_eq!(v.pixel_dimensions(), (1920, 1080));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), Some((2, 15)));
            }
            _ => panic!(),
        }

        // audio stream
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            &(prefix.to_string() + "/track1")
        );
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "pcma");
        assert_eq!(p.streams[1].rtp_payload_type, 8);
        assert_eq!(p.streams[1].clock_rate, 8_000);
        assert_eq!(p.streams[1].channels, NonZeroU16::new(1));
        match p.streams[1].parameters().unwrap() {
            Parameters::Audio(_) => {}
            _ => panic!(),
        };
    }

    /// [GW Security GW4089IP](https://github.com/scottlamb/moonfire-nvr/wiki/Cameras:-GW-Security#gw4089ip),
    /// main stream (high-res, audio).
    #[test]
    fn gw_main() {
        // DESCRIBE.
        let base = "rtsp://192.168.1.110:5050/H264?channel=1&subtype=0&unicast=true&proto=Onvif";
        let mut p = parse_describe(base, include_bytes!("testdata/gw_main_describe.txt")).unwrap();
        assert_eq!(p.control.as_str(), base);
        assert!(!p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 2);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            "rtsp://192.168.1.110:5050/H264?channel=1&subtype=0&unicast=true&proto=Onvif/video"
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.4D002A");
                assert_eq!(v.pixel_dimensions(), (1920, 1080));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), None);
            }
            _ => panic!(),
        }

        // audio stream
        assert_eq!(
            p.streams[1].control.as_ref().unwrap().as_str(),
            "rtsp://192.168.1.110:5050/H264?channel=1&subtype=0&unicast=true&proto=Onvif/audio"
        );
        assert_eq!(p.streams[1].media, "audio");
        assert_eq!(p.streams[1].encoding_name, "pcmu"); // rtpmap wins over static list.
        assert_eq!(p.streams[1].rtp_payload_type, 8);
        assert_eq!(p.streams[1].clock_rate, 8_000);
        assert_eq!(p.streams[1].channels, NonZeroU16::new(1));
        match p.streams[1].parameters().unwrap() {
            Parameters::Audio(_) => {}
            _ => panic!(),
        };

        // SETUP.
        let setup_response = response(include_bytes!("testdata/gw_main_setup_video.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "9a90de54".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, None);
        p.streams[0].state = StreamState::Init(StreamStateInit {
            ssrc: None,
            initial_seq: None,
            initial_rtptime: None,
        });

        let setup_response = response(include_bytes!("testdata/gw_main_setup_audio.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "9a90de54".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(2));
        assert_eq!(setup_response.ssrc, None);
        p.streams[1].state = StreamState::Init(StreamStateInit {
            ssrc: None,
            initial_seq: None,
            initial_rtptime: None,
        });

        // PLAY.
        super::parse_play(
            &response(include_bytes!("testdata/gw_main_play.txt")),
            &mut p,
        )
        .unwrap();
        // The RTP-Info url= isn't in the expected format, so its contents are skipped.
        match &p.streams[0].state {
            StreamState::Init(s) => {
                assert_eq!(s.initial_seq, None);
                assert_eq!(s.initial_rtptime, None);
            }
            _ => panic!(),
        };
        match &p.streams[1].state {
            StreamState::Init(s) => {
                assert_eq!(s.initial_seq, None);
                assert_eq!(s.initial_rtptime, None);
            }
            _ => panic!(),
        };
    }

    /// [GW Security GW4089IP](https://github.com/scottlamb/moonfire-nvr/wiki/Cameras:-GW-Security#gw4089ip),
    /// sub stream (low-res, no audio).
    #[test]
    fn gw_sub() {
        // DESCRIBE.
        let base = "rtsp://192.168.1.110:5049/H264?channel=1&subtype=1&unicast=true&proto=Onvif";
        let mut p = parse_describe(base, include_bytes!("testdata/gw_sub_describe.txt")).unwrap();
        assert_eq!(
            p.control.as_str(),
            "rtsp://192.168.1.110:5049/H264?channel=1&subtype=1&unicast=true&proto=Onvif"
        );
        assert!(!p.accept_dynamic_rate);

        assert_eq!(p.streams.len(), 1);

        // H.264 video stream.
        assert_eq!(
            p.streams[0].control.as_ref().unwrap().as_str(),
            "rtsp://192.168.1.110:5049/H264?channel=1&subtype=1&unicast=true&proto=Onvif/video"
        );
        assert_eq!(p.streams[0].media, "video");
        assert_eq!(p.streams[0].encoding_name, "h264");
        assert_eq!(p.streams[0].rtp_payload_type, 96);
        assert_eq!(p.streams[0].clock_rate, 90_000);
        match p.streams[0].parameters().unwrap() {
            Parameters::Video(v) => {
                assert_eq!(v.rfc6381_codec(), "avc1.4D001E");
                assert_eq!(v.pixel_dimensions(), (720, 480));
                assert_eq!(v.pixel_aspect_ratio(), None);
                assert_eq!(v.frame_rate(), None);
            }
            _ => panic!(),
        }

        // SETUP.
        let setup_response = response(include_bytes!("testdata/gw_sub_setup.txt"));
        let setup_response = super::parse_setup(&setup_response).unwrap();
        assert_eq!(
            setup_response.session,
            SessionHeader {
                id: "9b0d0e54".into(),
                timeout_sec: 60
            }
        );
        assert_eq!(setup_response.channel_id, Some(0));
        assert_eq!(setup_response.ssrc, None);
        p.streams[0].state = StreamState::Init(StreamStateInit {
            ssrc: None,
            initial_seq: None,
            initial_rtptime: None,
        });

        // PLAY.
        super::parse_play(
            &response(include_bytes!("testdata/gw_sub_play.txt")),
            &mut p,
        )
        .unwrap();
        match &p.streams[0].state {
            StreamState::Init(s) => {
                assert_eq!(s.initial_seq, Some(273));
                assert_eq!(s.initial_rtptime, Some(1621810809));
            }
            _ => panic!(),
        };
    }
}
