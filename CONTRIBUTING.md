# Contributing to Retina

## Testing

Quick test: `cargo test --all-features`

Before sending a change, at least:

* `cargo clippy --all-targets -- -D warnings`
* `cargo fmt --check --all`

CI has additional checks, including that:

* the full workspace builds, including example programs
* the crate works with its Minimum Supported Rust Version (MSRV)
* `--no-default-features` builds as well
* a quick run of fuzz tests passes

### Timers, paused time, and auto-advance

Many client tests in `src/client/mod.rs` drive a `Session` against a mock
server under `#[tokio::test(start_paused = true)]`, so they don't wait on
real timers. With paused time, tokio *auto-advances* the clock: once every
task is idle, the runtime does one non-blocking I/O poll and, if nothing is
ready, jumps the clock straight to the next registered timer. (A timer is
registered on its first poll and stays registered until drop or reset,
even if nothing polls it again.)

This makes such tests sensitive to anything that's in flight but not yet
visible to that I/O poll. Data just written to a loopback TCP socket may not
be readable yet, especially on macOS, so the clock can jump to, say, a 30 s
keepalive deadline in the middle of what should be an instantaneous
exchange.

* **Use `connect_to_mock` to establish mock TCP connections.**
  This uses a userspace-only pair so reads are visible to tokio immediately
  after write.
* **Careful with UDP sockets.** These currently use real kernel-level
  sockets and thus can cause unexpected time jumps.
  * If your test should complete immediately, it's okay to use real rather
    than mocked time.
  * Consider refactoring the UDP codepath to use mocks like TCP.
  * As a last resort, test code can temporarily remove timers (put a `None`
    in `Option<Pin<Box<Sleep>>>`) or replace them with ones that have never
    been polled.
* **Don't expect same-deadline timers to be ordered.** tokio does not
  guarantee this. If you write a test that sleeps until the instant a
  keepalive timer is due and expects it to have fired, your test will be
  flaky! Sleep until slightly later instead.
* **Expect millisecond precision.** tokio rounds timer deadlines up to a whole
  millisecond. (To put the clock at a particular sub-millisecond instant, use
  `tokio::time::advance` explicitly.) Otherwise times are exact; you can
  use `assert_eq!` rather than expecting a range.
* **Handle timers as in production.** Prefer showing the code works with
  e.g. keepalives rather than disabling them.
