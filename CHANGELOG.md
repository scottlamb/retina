## unreleased

*   warn when connecting via TCP to a known-broken live555 server version.
*   improve compatibility with Geovision cameras (work in progress).
*   UDP fixes.

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

## v0.1.0 (2021-08-13)

*   use `SET_PARAMETERS` rather than `GET_PARAMETERS` for keepalives.
    The latter doesn't work with GW Security GW4089IP cameras.
*   removed `rtcp` dependency. Fixes
    [#8](https://github.com/scottlamb/retina/issues/8). Avoids picking up
    various transitive dependencies needed by later versions of the `rtcp`
    crate, including `tokio`. (`retina`'s own `tokio` dependency will likely
    become optional in a future version.)

## v0.0.5 (2021-07-08)

*   BREAKING CHANGE: New opaque error type with more uniform, richer error
    messages. No more `failure` dependency.
*   BREAKING CHANGE: `retina::client::Stream::parameters` now returns parameters
    by value. This allows shrinking depacketizer types.
*   BREAKING CHANGE: `retina::codec::VideoFrame::new_parameters` is now boxed.
    This allows shrinking `VideoFrame` and `CodecItem` by 80 bytes each (on
    64-bit platforms). The box is only rarely populated.
*   in `client mp4` example, handle an initial video parameter change correctly.

## v0.0.4 (2021-06-28)

*   bugfix: Retina stopped receiving packets after receiving a keepalive response.

## v0.0.3 (2021-06-28)

*   BREAKING CHANGE: `Session<Playing>` now directly implements `Stream` instead of
    through `pkts()`.
*   Performance improvements.

## v0.0.2 (2021-06-25)

*   BREAKING CHANGE: Video frames are now provided as a single, contiguous `Bytes`, and
    H.264 depacketization is more efficient ([#4](https://github.com/scottlamb/retina/issues/4)).

## v0.0.1 (2021-06-09)

Initial release.
