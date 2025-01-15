## unreleased

*   improve some error messages on bad H.264 `sprop-parameter-sets`
*   interoperate with V380 cameras by interpreting Annex B sequences in contexts
    where single NALs are otherwise expected.
    (Fixes [#68](https://github.com/scottlamb/retina/issues/68),
    [[#108](https://github.com/scottlamb/retina/issues/108)]).

## `v0.4.10` (2024-08-19)

*   update `base64` dep to 0.22
*   update minimum Rust version to 1.70.

## `v0.4.9` (2024-08-19)

*   added helpers for building `.mp4` `VisualSampleEntry` and `AudioSampleEntry`
    for H.264, MJPEG, and AAC.
*   shrunk `VideoParameters` from 112 bytes to 88 bytes and `AudioParameters`
    from 80 bytes to 64 bytes (measured on a 64-bit platform).

## `v0.4.8` (2024-05-26)

*   support MJPEG codec (contribution from [zanshi](https://github.com/zanshi))
*   permit `MP2T/` protocol in media description (contribution from
    (yujincheng08)[https://github.com/yujincheng08)]).
*   [#102](https://github.com/scottlamb/retina/102): support Reolink cameras
    which have extraneous bytes following the SPS.

## `v0.4.7` (2024-01-08)

*   support servers that do not set `Content-Type` on `DESCRIBE` responses

## `v0.4.6` (2023-12-29)

*   add default User-Agent header
*   add policy for handling session IDs. Required for some broken cameras which
    can change the session ID between `SETUP` calls.
*   ignore connection refused errors triggered by the firewall punch-through
    packets.
*   improve several vague or misleading log messages.
*   fix inverted logic in live555 bug detection, introduced with `v0.3.10`.
*   ignore `seq=0` and `seq=1` in `PLAY` response's `RTP-Info` header by default.
    These values are known to be set erroneously by the Hikvision DS-2CD2032-I
    and Tapo C320WS, respectively.
*   customizable behavior for RTCP packets with unknown ssrcs, now defaulting to
    ignoring them. This also is necessary to interoperate with the Tapo C320WS.
*   improve some incorrect, misleading, and/or uninformative logging.
*   minimum Rust is now 1.67.

## `v0.4.5` (2023-02-02)

*   minimum Rust version is now 1.64.
*   upgrade to `rtsp-types` 0.0.5, which ignores trailing whitespace in RTSP
    headers. This fixes errors when communicating with some Longse cameras
    ([#77](https://github.com/scottlamb/retina/pull/77)).
*   remove obsolete workaround for GW security GW security GW4089IP's bad out-of-band parameters.
    Instead, we treat them as unparseable and ignore them as described in the
    `v0.4.2` notes below.

## `v0.4.4` (2022-12-26)

*   improve interop with Ubiquiti cameras by ignoring `fmtp` attributes in
    SDP which have nothing (no required SP, no data) after the payload type.
*   fix parsing of RTP packets with extensions, which broke with `v0.4.0`
    (2e34bf92).

## `v0.4.3` (2022-09-28)

*   upgrade version of `h264-reader` crate. Compatibility note: Retina may now
    be stricter about parsing H.264 parameters (SPS/PPS). In practice, with some
    cameras this means unparseable "out-of-line" parameters (specified in the
    SDP) will be ignored in favor of parseable "in-line" parameters (specified
    within the RTP data stream).

## `v0.4.2` (2022-09-28)

*   ignore unparseable SDP media, improving compatibility with TP-Link cameras,
    as described in [scottlamb/moonfire-nvr#238](https://github.com/scottlamb/moonfire-nvr/issues/238).

## `v0.4.1` (2022-08-09)

*   Send keepalives at every half-session-timeout rather than a fixed 30-second
    interval. This allows persistent connections to servers that have timeouts
    shorter than 30 seconds.
*   Use `OPTIONS` for initial keepalive, and only switch to `SET_PARAMETER` if
    the server advertises its support. This allows persistent connections to
    `rtsp-simple-server` v0.19.3, which does not support the latter method and
    drops the connection on receiving unsupported methods.

## `v0.4.0` (2022-05-17)

*   BREAKING: remove deprecated `retina::client::Session<Playing>::teardown` and
    `retina::client::Demuxed::teardown`; made private some items already
    `#[doc(hidden)]`.
*   BREAKING: `retina::client::Session<Described>::setup` takes a new
    `SetupOptions` argument for future expansion.
*   BREAKING: the transport to use is configured per-stream as part of
    `retina::SetupOptions` (rather than the prior `retina::SessionOptions`) and
    takes per-transport options for future expansion.
*   BREAKING: `retina::StreamContext` has been split out of
    `retina::PacketContext`. Both must be printed to provide the same
    information as before. This change reduces how much data needs to be copied
    with each packet.
*   BREAKING: `PacketItem` and `CodecItem` are now `#[non_exhaustive]` for
    future expansion.
*   BREAKING: `retina::client::rtp::Packet` is now
    `retina::rtp::ReceivedPacket`, and field access has been removed in favor
    of accessors.
*   BREAKING: `retina::client::PacketItem::RtpPacket` has been renamed to
    `retina::client::PacketItem::Rtp`.
*   BREAKING: `retina::client::PacketItem::SenderReport` has been replaced with
    `retina::client::PacketItem::Rtcp`, to expose full RTCP compound packets.
    Likewise `retina::codec::CodecItem`.
*   BREAKING: `retina::codec::Parameters` is now `retina::codec::ParametersRef`,
    which references parameters stored within the `Stream` to reduce copying.
*   minimum Rust version is now 1.59.

## `v0.3.10` (2022-05-09)

*   ignore unparseable `rtptime` values in the `PLAY` response's `RTP-Info` header.
    This improves compatibility with the OMNY M5S2A 2812 camera, as described in
    [scottlamb/moonfire-nvr#224](https://github.com/scottlamb/moonfire-nvr/issues/224).

## `v0.3.9` (2022-04-12)

*   camera interop: eliminate `bad clockrate in rtpmap` errors with cameras that
    (incorrectly) add trailing spaces to this SDP parameter, as described at
    [scottlamb/moonfire-nvr#213](https://github.com/scottlamb/moonfire-nvr/issues/213#issue-1190760423).
*   camera interop: allow ignoring RTSP interleaved data messages on unassigned
    channels, also described at [scottlamb-moonfire-nvr#213](https://github.com/scottlamb/moonfire-nvr/issues/213#issuecomment-1089411093).
*   camera interop: when using TCP, default to attempting a `TEARDOWN`  before
    closing the connection, to improve behavior with cameras that have the
    live555 stale session bug but do not advertise it.
*   clarify `Session`'s expectations for tokio runtimes.
*   additional diagnostics/logging on certain camera failures.

## `v0.3.8` (2022-03-08)

*   fix depacketization of fragmented AAC frames
*   [#52](https://github.com/scottlamb/retina/issues/52): allow compatibility
    with cameras that incorrectly omit the SDP origin line.
*   fix panic if RTSP server precedes a data message with a CRLF.
*   expose SDP framerate via `retina::client::Stream::framerate`.

## `v0.3.7` (2022-01-28)

*   [#50](https://github.com/scottlamb/retina/pull/50): fix a panic on certain
    invalid H.264 `sprop-parameter-sets`
*   documentation improvements

## `v0.3.6` (2021-12-29)

*   correctly expire stale session entries that track live555 stale file
    descriptor sessions.
    See [moonfire-nvr#184](https://github.com/scottlamb/moonfire-nvr/issues/184).
*   ignore (rather than error on) spurious RTP data packets between the `PLAY`
    request and response. These are sent by some versions of
    [v4l2rtspserver](https://github.com/mpromonet/v4l2rtspserver).

## `v0.3.5` (2021-11-30)

*   [#42](https://github.com/scottlamb/retina/issues/42): support servers that
    don't send out-of-band H.264 parameters or send invalid parameters; wait for
    in-band parameters in this case. The in-band parameters must be valid.
*   documentation improvements.

## `v0.3.4` (2021-10-26)

*   use `rtsp-types` 0.0.3, and thus `nom` 7.0.

## `v0.3.3` (2021-10-20)

*   [#25](https://github.com/scottlamb/retina/issues/25): better HTTP
    authentication support via the new [`http-auth`
    crate](https://crates.io/crates/http-auth). Before, `retina` would only
    authenticate properly if the first requested challenge was `Digest`. Now, it
    will pick out a `Digest` or `Basic` challenge from a list.

## `v0.3.2` (2021-09-29)

*   better `TEARDOWN` handling, which often avoids the need to wait for session
    expiration ([(#34](https://github.com/scottlamb/retina/issues/34)).

## `v0.3.1` (2021-09-09)

*   warn when connecting via TCP to a known-broken live555 server version.
*   improve Geovision compatibility by skipping its strange RTP packets with
    payload type 50.
*   UDP fixes.
*   improve compatibility with cameras with non-compliant SDP, including
    Anpviz ([#26](https://github.com/scottlamb/retina/issues/26) and
    Geovision ([#33])(https://github.com/scottlamb/retina/issues/33)).
*   new mechanism to more reliably send `TEARDOWN` requests.

## `v0.3.0` (2021-08-31)

*   BREAKING CHANGE: [#30](https://github.com/scottlamb/retina/issues/30):
    experimental UDP support. Several `RtspMessageContext` fields have been
    replaced with `PacketContext`.
*   BREAKING CHANGE: remove `retina::client::SessionOptions::ignore_spurious_data`. This
    was an attempted workaround for old live555 servers
    ([#17](https://github.com/scottlamb/retina/issues/17)) that was ineffective.
*   [#22](https://github.com/scottlamb/retina/issues/22): fix handling of
    44.1 kHz AAC audio.

## `v0.2.0` (2021-08-20)

*   BREAKING CHANGE: `retina::client::Session::describe` now takes a new
    `options: SessionOptions`. The `creds` has moved into the `options`, along
    with some new options.
*   BREAKING CHANGE: renamed `PlayPolicy` to `PlayOptions` for consistency.
*   Added options to work around bugs found in Reolink cameras.
*   [#9](https://github.com/scottlamb/retina/issues/9). Improve compatibility
    with how some cameras handle the `control` and `RTP-Info` urls. This
    adopts a URL joining behavior which isn't RFC-compliant but seems to
    be more compatible in practice.

## `v0.1.0` (2021-08-13)

*   use `SET_PARAMETERS` rather than `GET_PARAMETERS` for keepalives.
    The latter doesn't work with GW Security GW4089IP cameras.
*   removed `rtcp` dependency. Fixes
    [#8](https://github.com/scottlamb/retina/issues/8). Avoids picking up
    various transitive dependencies needed by later versions of the `rtcp`
    crate, including `tokio`. (`retina`'s own `tokio` dependency will likely
    become optional in a future version.)

## `v0.0.5` (2021-07-08)

*   BREAKING CHANGE: New opaque error type with more uniform, richer error
    messages. No more `failure` dependency.
*   BREAKING CHANGE: `retina::client::Stream::parameters` now returns parameters
    by value. This allows shrinking depacketizer types.
*   BREAKING CHANGE: `retina::codec::VideoFrame::new_parameters` is now boxed.
    This allows shrinking `VideoFrame` and `CodecItem` by 80 bytes each (on
    64-bit platforms). The box is only rarely populated.
*   in `client mp4` example, handle an initial video parameter change correctly.

## `v0.0.4` (2021-06-28)

*   bugfix: Retina stopped receiving packets after receiving a keepalive response.

## `v0.0.3` (2021-06-28)

*   BREAKING CHANGE: `Session<Playing>` now directly implements `Stream` instead of
    through `pkts()`.
*   Performance improvements.

## `v0.0.2` (2021-06-25)

*   BREAKING CHANGE: Video frames are now provided as a single, contiguous `Bytes`, and
    H.264 depacketization is more efficient ([#4](https://github.com/scottlamb/retina/issues/4)).

## `v0.0.1` (2021-06-09)

Initial release.
