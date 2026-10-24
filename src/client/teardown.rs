// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Ending a session on the server; see [`TeardownCore`].

// Without the feature, only what `Session` uses is reachable.
#![cfg_attr(not(feature = "unstable-sans-io"), allow(dead_code))]

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};

use log::debug;
use url::Url;

use super::conn::{ConnCore, Response, ResponseMode};
use super::{Error, SessionGroup};
use crate::buf::MarkBuf;
use crate::error::ErrorInt;
use crate::rtsp::msg::{self, OwnedMessage, StatusCode};
use crate::{ConnectionContext, WallTime};

const EXISTING_CONN_TIMEOUT: Duration = Duration::from_secs(5);
const FRESH_CONN_INITIAL_TIMEOUT: Duration = Duration::from_secs(1);
const FRESH_CONN_MAX_TIMEOUT: Duration = Duration::from_secs(16);

/// What a [`TeardownCore`] needs from the caller, from [`TeardownCore::poll`].
///
/// Each deadline is at most the session's expiration.
#[derive(Debug)]
#[non_exhaustive]
pub enum TeardownAction {
    /// Do I/O on the current connection: write [`TeardownCore::transmit_buf`]
    /// and read into [`TeardownCore::read_buf`], calling
    /// [`TeardownCore::handle_eof`] or [`TeardownCore::handle_io_error`] as
    /// appropriate. Poll again after reading anything, or at `deadline`.
    Io { deadline: Instant },

    /// Close the current connection, if any, and open a fresh one to the host
    /// and port of [`TeardownCore::url`], then call
    /// [`TeardownCore::connected`] (or, on failure,
    /// [`TeardownCore::handle_io_error`]). Poll again after that, or at
    /// `deadline` if still connecting.
    Connect { deadline: Instant },

    /// Close the current connection, if any, and poll again at `until`.
    Wait { until: Instant },

    /// Finished: the server confirmed the session is gone, or Retina has
    /// decided to let it expire, either because the session has reached its
    /// expiration or because the policy says one attempt is enough. Further
    /// polls return the same.
    ///
    /// Failed attempts are logged at debug level, and reported to the
    /// session's [`SessionGroup`], if any.
    Done,
}

/// The sans-I/O state of ending a session on the server, from
/// [`super::SessionCore::into_teardown`].
///
/// This makes `TEARDOWN` attempts per the [`super::TeardownPolicy`]: first on
/// the session's own RTSP connection, then (unless the policy says to try
/// only once) on fresh connections, with growing timeouts, until success or
/// the session's expiration, after which the server has forgotten it anyway.
/// A dropped [`super::Session`] does the same in the background.
///
/// The caller drives it by calling [`TeardownCore::poll`] and doing what each
/// [`TeardownAction`] says until [`TeardownAction::Done`]. The first
/// [`TeardownAction::Io`] is on the connection the session used. Data
/// already received on it, and bytes not yet written, carry over, so keep
/// using it as before.
///
/// If the session has a [`super::SessionGroup`], it's tracked there until this
/// finishes. Dropping this before then leaves the session tracked until
/// expiration, with a failed attempt for [`SessionGroup::await_teardown`].
pub struct TeardownCore {
    conn: ConnCore,

    /// The `TEARDOWN` request, minus the `CSeq` and authentication headers
    /// added for each attempt.
    req: OwnedMessage,
    session_id: msg::HeaderValue,
    url: Url,
    just_try_once: bool,
    expires: Instant,

    /// The timeout for the next attempt on a fresh connection.
    next_timeout: Duration,
    state: State,

    /// The session's group and seqnum within it, until finished.
    tracked: Option<(Arc<SessionGroup>, u64)>,
}

enum State {
    /// Attempt `attempt` (with 0 meaning the session's own connection) is in
    /// progress.
    Attempting {
        attempt: u32,
        deadline: Instant,
    },

    /// Waiting for the caller to connect for fresh attempt `attempt`.
    Connecting {
        attempt: u32,
        deadline: Instant,
    },

    /// Waiting out a failed attempt's deadline before starting attempt `next`,
    /// to avoid going crazy when the server fails quickly.
    Backoff {
        next: u32,
        until: Instant,
    },

    Done,
}

impl TeardownCore {
    /// Starts tearing down a session, with a first attempt on `conn`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        mut conn: ConnCore,
        req: OwnedMessage,
        session_id: msg::HeaderValue,
        url: Url,
        just_try_once: bool,
        expires: Instant,
        tracked: Option<(Arc<SessionGroup>, u64)>,
        now: Instant,
    ) -> Self {
        debug!(
            "TEARDOWN {} starting for URL {}",
            &*session_id,
            url.as_str()
        );

        // A request may have been in progress when the session was dropped.
        // Its response, if any, will be ignored as unrelated.
        conn.abandon_pending();
        let deadline = now + EXISTING_CONN_TIMEOUT;
        let send_result = conn.send(ResponseMode::Teardown, req.clone());
        let mut this = Self {
            conn,
            req,
            session_id,
            url,
            just_try_once,
            expires,
            next_timeout: FRESH_CONN_INITIAL_TIMEOUT,
            state: State::Attempting {
                attempt: 0,
                deadline,
            },
            tracked,
        };
        if let Err(e) = send_result {
            this.attempt_failed(0, deadline, e, now, false);
        }
        this
    }

    /// Returns the URL the `TEARDOWN` is sent to. Fresh connections go to its
    /// host and port (by default, 554).
    pub fn url(&self) -> &Url {
        &self.url
    }

    /// Returns the session's assumed expiration time, after which Retina
    /// gives up.
    pub fn expires(&self) -> Instant {
        self.expires
    }

    #[cfg(feature = "tokio")]
    pub(super) fn options(&self) -> &super::SessionOptions {
        &self.conn.options
    }

    /// Returns what to do next.
    pub fn poll(&mut self, now: Instant) -> TeardownAction {
        loop {
            if !matches!(self.state, State::Done) && now >= self.expires {
                debug!(
                    "TEARDOWN {} stopped on session expiration",
                    &*self.session_id
                );
                self.finish();
            }
            match self.state {
                State::Attempting { attempt, deadline } => {
                    if let Some(r) = self.conn.poll_response(now) {
                        match status(r) {
                            Ok(status) => {
                                debug!(
                                    "TEARDOWN {} attempt {} succeeded (status {}).",
                                    &*self.session_id,
                                    attempt,
                                    u16::from(status)
                                );
                                self.finish();
                            }
                            Err(e) => self.attempt_failed(attempt, deadline, e, now, false),
                        }
                        continue;
                    }
                    if now >= deadline {
                        self.attempt_failed(attempt, deadline, wrap!(ErrorInt::Timeout), now, true);
                        continue;
                    }
                    return TeardownAction::Io {
                        deadline: deadline.min(self.expires),
                    };
                }
                State::Connecting { attempt, deadline } => {
                    if now >= deadline {
                        self.attempt_failed(attempt, deadline, wrap!(ErrorInt::Timeout), now, true);
                        continue;
                    }
                    return TeardownAction::Connect {
                        deadline: deadline.min(self.expires),
                    };
                }
                State::Backoff { next, until } => {
                    if now >= until {
                        self.start_connecting(next, now);
                        continue;
                    }
                    return TeardownAction::Wait {
                        until: until.min(self.expires),
                    };
                }
                State::Done => return TeardownAction::Done,
            }
        }
    }

    /// Returns the bytes to write to the current connection, in order.
    ///
    /// The first slice is empty iff there's nothing to write. After writing,
    /// call [`TeardownCore::advance_transmit`].
    pub fn transmit_buf(&self) -> (&[u8], &[u8]) {
        match self.state {
            State::Attempting { .. } => self.conn.transmit_buf(),
            _ => (&[], &[]),
        }
    }

    /// Notes that the first `n` bytes of [`TeardownCore::transmit_buf`] have
    /// been written.
    ///
    /// # Panics
    ///
    /// If `n` exceeds the bytes available.
    pub fn advance_transmit(&mut self, n: usize) {
        self.conn.advance_transmit(n);
    }

    /// Returns the buffer the caller should fill with bytes received on the
    /// current connection, via `spare_capacity` and `advance_end`.
    pub fn read_buf(&mut self) -> &mut MarkBuf {
        self.conn.read_buf()
    }

    /// Notes that the peer has closed the current connection.
    pub fn handle_eof(&mut self) {
        self.conn.eof = true;
    }

    /// Notes that the fresh connection for [`TeardownAction::Connect`] is
    /// established, from `local_addr` to `peer_addr`.
    ///
    /// # Panics
    ///
    /// Unless the last poll returned [`TeardownAction::Connect`].
    pub fn connected(&mut self, local_addr: SocketAddr, peer_addr: SocketAddr, now: Instant) {
        let State::Connecting { attempt, deadline } = self.state else {
            panic!("connected requires TeardownAction::Connect");
        };
        self.conn.reconnect(ConnectionContext {
            local_addr,
            peer_addr,
            established_wall: WallTime::now(),
        });
        match self.conn.send(ResponseMode::Teardown, self.req.clone()) {
            Ok(()) => self.state = State::Attempting { attempt, deadline },
            Err(e) => self.attempt_failed(attempt, deadline, e, now, false),
        }
    }

    /// Notes a failure to connect, read, or write, ending the current attempt.
    pub fn handle_io_error(&mut self, source: std::io::Error, now: Instant) {
        let e = match self.state {
            State::Attempting { .. } => self.conn.read_error(source, now),
            State::Connecting { .. } => wrap!(ErrorInt::ConnectError(source)),
            _ => return,
        };
        self.fail_attempt(e, now);
    }

    /// Ends the current attempt (if any) with `e`.
    pub(super) fn fail_attempt(&mut self, e: Error, now: Instant) {
        if let State::Attempting { attempt, deadline } | State::Connecting { attempt, deadline } =
            self.state
        {
            self.attempt_failed(attempt, deadline, e, now, false);
        }
    }

    fn start_connecting(&mut self, attempt: u32, now: Instant) {
        self.state = State::Connecting {
            attempt,
            deadline: now + self.next_timeout,
        };
    }

    /// Moves on from a failed attempt, which `timed_out` or otherwise failed
    /// before its `deadline`.
    fn attempt_failed(
        &mut self,
        attempt: u32,
        deadline: Instant,
        e: Error,
        now: Instant,
        timed_out: bool,
    ) {
        if attempt == 0 {
            debug!(
                "TEARDOWN {} on existing conn failed: {}",
                &*self.session_id, e
            );
            if self.just_try_once {
                // TCP, auto teardown, server not known to be affected by the
                // live555 TCP session bug, tried one TEARDOWN on the existing
                // conn (just in case the server really does have that bug),
                // closed the connection. Good enough.
                debug!(
                    "Letting session {} expire; use TeardownPolicy::Always to try harder",
                    &*self.session_id
                );
                self.finish();
                return;
            }

            // Retry with a new connection, without waiting for the attempt
            // deadline.
            //
            // A particularly likely case is when the session was dropped due
            // to corrupt message. This attempt will inevitably fail reading
            // the same corrupt message. It's worth trying anyway because the
            // server may actually execute the TEARDOWN, even though we can't
            // read the response.
            //
            // The first try with a fresh connection is likely to be more
            // successful, and maybe will simply confirm the session is
            // already destroyed. Do it soon.
            //
            // Also, don't note the failure in the group, so await_teardown()
            // won't fail early. Let's at least do an attempt with a fresh
            // connection first.
            self.start_connecting(1, now);
            return;
        }
        debug!(
            "TEARDOWN {} fresh connection attempt {} failed: {}",
            &*self.session_id, attempt, e
        );
        if let Some((group, seqnum)) = &self.tracked {
            group.note_teardown_failure(*seqnum, e.clone());
        }
        self.next_timeout = std::cmp::min(self.next_timeout * 2, FRESH_CONN_MAX_TIMEOUT);
        if timed_out {
            self.start_connecting(attempt + 1, now);
        } else {
            self.state = State::Backoff {
                next: attempt + 1,
                until: deadline,
            };
        }
    }

    fn finish(&mut self) {
        if let Some((group, seqnum)) = self.tracked.take() {
            log::trace!(
                "Clearing session {:?}/{} for id {:?}",
                group.debug_id(),
                seqnum,
                &*self.session_id
            );
            if !group.try_remove_seqnum(seqnum) {
                // It may have been forgotten on expiration.
                debug!(
                    "Unable to find session {:?}/{} for id {:?} on TEARDOWN",
                    group.debug_id(),
                    seqnum,
                    &*self.session_id
                );
            }
        }
        self.state = State::Done;
    }
}

impl Drop for TeardownCore {
    fn drop(&mut self) {
        if let Some((group, seqnum)) = self.tracked.take() {
            debug!("TEARDOWN {} abandoned before completion", &*self.session_id);
            group.note_teardown_failure(
                seqnum,
                wrap!(ErrorInt::FailedPrecondition(
                    "TEARDOWN abandoned before completion".into()
                )),
            );
        }
    }
}

/// Drives `core` to completion in the background, starting with `conn` (the
/// session's connection).
#[cfg(feature = "tokio")]
pub(super) async fn background_teardown(
    mut core: TeardownCore,
    mut conn: Option<crate::tokio::Connection>,
) {
    use tokio::time::{Instant as TokioInstant, sleep_until};

    // Use tokio's clock, to match the timers. Outside tests that pause time,
    // it's the same as `std::time::Instant::now()`.
    let now = || TokioInstant::now().into_std();
    loop {
        match core.poll(now()) {
            TeardownAction::Io { deadline } => {
                let Some(c) = conn.as_mut() else {
                    core.fail_attempt(
                        wrap!(ErrorInt::FailedPrecondition("no connection".into())),
                        now(),
                    );
                    continue;
                };
                let r = tokio::select! {
                    r = std::future::poll_fn(|cx| poll_io(cx, c, &mut core)) => Some(r),
                    _ = sleep_until(TokioInstant::from_std(deadline)) => None,
                };
                if let Some(Err(e)) = r {
                    core.fail_attempt(e, now());
                }
            }
            TeardownAction::Connect { deadline } => {
                conn = None;
                let r = tokio::select! {
                    r = super::connect(core.url(), core.options()) => Some(r),
                    _ = sleep_until(TokioInstant::from_std(deadline)) => None,
                };
                match r {
                    Some(Ok(c)) => {
                        let ctx = c.ctx();
                        core.connected(ctx.local_addr, ctx.peer_addr, now());
                        conn = Some(c);
                    }
                    Some(Err(e)) => core.fail_attempt(e, now()),
                    None => {}
                }
            }
            TeardownAction::Wait { until } => {
                conn = None;
                sleep_until(TokioInstant::from_std(until)).await;
            }
            TeardownAction::Done => return,
        }
    }
}

/// Writes what `core` has to write to `conn`, and returns once something has
/// been read.
#[cfg(feature = "tokio")]
fn poll_io(
    cx: &mut std::task::Context<'_>,
    conn: &mut crate::tokio::Connection,
    core: &mut TeardownCore,
) -> std::task::Poll<Result<(), Error>> {
    use std::task::Poll;
    loop {
        let bufs = core.transmit_buf();
        if bufs.0.is_empty() {
            break;
        }
        match conn.poll_write_vectored(cx, bufs) {
            Poll::Ready(Ok(n)) => core.advance_transmit(n),
            Poll::Ready(Err(e)) => return Poll::Ready(Err(wrap!(e))),
            Poll::Pending => break,
        }
    }
    match conn.poll_read(cx, core.read_buf()) {
        Poll::Ready(Ok(0)) => {
            core.handle_eof();
            Poll::Ready(Ok(()))
        }
        Poll::Ready(Ok(_)) => Poll::Ready(Ok(())),
        Poll::Ready(Err(e)) => {
            let now = tokio::time::Instant::now().into_std();
            Poll::Ready(Err(core.conn.read_error(e, now)))
        }
        Poll::Pending => Poll::Pending,
    }
}

/// Interprets the result of a `TEARDOWN` request, returning the status if the
/// session is gone.
pub(super) fn status(r: Result<Response, Error>) -> Result<StatusCode, Error> {
    let e = match r {
        Ok(resp) => return Ok(resp.head.status_code),
        Err(e) => e,
    };

    // Use a second match clause to look inside the Arc.
    match *e.0 {
        ErrorInt::RtspResponseError { status, .. }
            if status == StatusCode::SESSION_NOT_FOUND ||

            // This is deeply unsatisfying, but at least the Hikvision
            // DS-2CD2032 with firmware V5.4.41 build 170312 exhibits the
            // following non-standard behavior:
            //
            // * the RTSP session is tied to a particular connection, even when
            //   streaming RTP over UDP. If the connection is dropped, the UDP
            //   packets stop flowing.
            // * a TEARDOWN on a fresh connection will always fail with
            //   status 500 Internal Server Error.
            //
            // This contradicts RFC 2326 section 1.1, which says "An RTSP
            // session is in no way tied to a transport-level connection such as
            // a TCP connection". Nonetheless, we'll go along with this for now
            // by assuming the session is gone when we get a 500 response.
            status == StatusCode::INTERNAL_SERVER_ERROR =>
        {
            Ok(status)
        }
        _ => Err(e),
    }
}
