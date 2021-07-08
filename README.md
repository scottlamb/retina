# retina

[![crates.io version](https://img.shields.io/crates/v/retina.svg)](https://crates.io/crates/retina)
[![Documentation](https://docs.rs/retina/badge.svg)](https://docs.rs/retina)
[![CI](https://github.com/scottlamb/retina/workflows/CI/badge.svg)](https://github.com/scottlamb/retina/actions?query=workflow%3ACI)

High-level RTSP multimedia streaming library, in Rust. Good support for
ONVIF RTSP/1.0 IP surveillance cameras, as needed by
[Moonfire NVR](https://github.com/scottlamb/moonfire-nvr). Works around
brokenness in cheap closed-source cameras.

Progress:

*   [x] client support
    *   [x] digest authentication.
    *   [x] RTP over TCP via RTSP interleaved channels.
    *   [ ] RTP over UDP.
    *   [x] RTSP/1.0.
    *   [ ] RTSP/2.0.
    *   [ ] SRTP.
    *   [ ] ONVIF backchannel support (for sending audio).
    *   [ ] ONVIF replay mode.
    *   [x] receiving RTCP Sender Reports (currently only uses the timestamp)
    *   [ ] sending RTCP Receiver Reports
*   [ ] server support
*   I/O modes
    *   [x] async with tokio
    *   [ ] async-std. (Most of the crate's code is independent of the async
        library, so I don't expect this would be too hard to add.)
    *   [ ] synchronous with std only
*   codec depacketization
    *   [x] video: H.264
        ([RFC 6184](https://datatracker.ietf.org/doc/html/rfc6184))
        *   [ ] SVC
        *   [ ] periodic infra refresh
        *   [x] multiple slices per picture
        *   [ ] multiple SPS/PPS
        *   [ ] interleaved mode
    *   audio
        *   [x] AAC
            *   [ ] interleaving
        *   [x] [RFC 3551](https://datatracker.ietf.org/doc/html/rfc3551)
            codecs: G.711, G.723, L8/L16
    *   [x] application: ONVIF metadata
*   [ ] uniform, documented API. (Currently haphazard in terms of naming, what
        fields are exposed directly vs use an accessors, etc.)
*   quality errors
*   *   [x] detailed error description text.
*   *   [ ] programmatically inspectable error type.
*   [ ] good functional testing coverage. (Currently lightly / unevenly tested.)
        Most depacketizers have no tests.)
*   [ ] fuzz testing. (In progress.)
*   [x] benchmark

Currently very unstable: expect breaking API changes at every release as I work
through items above.

Help welcome!

## Getting started

Try the `mp4` example. It streams from an RTSP server to a `.mp4` file until
you hit ctrl-C.

```
$ cargo run --example client mp4 --url rtsp://ip.address.goes.here/ --username admin --password test out.mp4
...
^C
```

## Acknowledgements

This builds on the whole Rust ecosystem. A couple folks have been especially
helpful:

*   Sebastian Dröge, author of
    [`rtsp-types`](https://crates.io/crates/rtsp-types)
*   David Holroyd, author of
    [`h264-reader`](https://crates.io/crates/h264-reader)

## Why "retina"?

It's a working name. Other ideas welcome. I started by looking at dictionary
words with the letters R, T, S, and P in order and picking out ones related to
video:

| `$ egrep '^r.*t.*s.*p' /usr/share/dict/words'` |                                                                              |
| ---------------------------------------------- | ---------------------------------------------------------------------------- |
| <b>r</b>e<b>t</b>ino<b>s</b>co<b>p</b>e        | close but too long, thus `retina`                                            |
| <b>r</b>e<b>t</b>ro<b>sp</b>ect                | good name for an NVR, but I already picked Moonfire                          |
| <b>r</b>o<b>t</b>a<b>s</b>co<b>p</b>e          | misspelling of "rotascope" (animation tool) or archaic name for "gyroscope"? |

## License

Your choice of MIT or Apache; see [LICENSE-MIT.txt](LICENSE-MIT.txt) or
[LICENSE-APACHE](LICENSE-APACHE.txt), respectively.
