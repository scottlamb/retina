# retina

[![CI](https://github.com/scottlamb/retina/workflows/CI/badge.svg)](https://github.com/scottlamb/retina/actions?query=workflow%3ACI)

High-level RTSP multimedia streaming library, in Rust. Good support for
IP surveillance cameras, as needed by
[Moonfire NVR](https://github.com/scottlamb/moonfire-nvr).

Progress:

*   [x] client support
*   *   [x] digest authentication
*   *   [x] RTP over TCP via RTSP interleaved channels.
*   *   [ ] RTP over UDP. (Shouldn't be hard but I haven't needed it.)
*   *   [ ] SRTP
*   *   [ ] ONVIF backchannel support (for sending audio).
*   [ ] server support
*   async 
*   *   [x] tokio
*   *   [ ] async-std. (Most of the crate's code is independent of the async
        library, so I don't expect this would be too hard to add.)
*   codec depacketization
*   *   [x] video: H.264
*   *   *   [ ] SVC
*   *   *   [ ] periodic infra refresh
*   *   *   [ ] partitioned slices
*   *   audio
*   *   *   [x] AAC
*   *   *   *   [ ] interleaving
*   *   *   [x] RFC 3551 codecs: G.711,G.723, L8/L16
*   *   [x] application: ONVIF metadata
*   [ ] uniform, documented API. (Currently haphazard in terms of naming, what
        fields are exposed directly vs use an accessors, etc.)
*   [ ] rich errors. (Currently uses untyped errors with the deprecated failure
        crate; some error messages are quite detailed, others aren't.)
*   [ ] released versions of all deps. (crates.io publishing requirement.)
*   [ ] good functional testing coverage. (Currently lightly / unevenly tested.
        The depacketizers have no test coverage, and there's at least one place
        left that can panic on bad input.)
*   [ ] fuzz testing

Help welcome!

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
