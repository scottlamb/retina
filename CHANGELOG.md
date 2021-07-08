## unreleased

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