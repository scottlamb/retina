## unreleased

*   New opaque error type with more uniform, richer error messages. No more
    `failure` dependency.

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