// Copyright (C) 2021 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

use bytes::Bytes;
use rtsp_types::{Method, Request};
use url::Url;

use super::{ResponseMode, RtspConnection, SessionOptions};
use crate::{error::ErrorInt, Error};

const EXISTING_CONN_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(5);
const FRESH_CONN_INITIAL_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(1);
const FRESH_CONN_MAX_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(16);

/// Handles `TEARDOWN` loop in the background, removing the stale session entry on success or
/// session expiry.
pub(super) async fn background_teardown(
    seqnum: Option<u64>,
    base_url: Url,
    session_id: Box<str>,
    options: SessionOptions,
    requested_auth: Option<digest_auth::WwwAuthenticateHeader>,
    conn: Option<RtspConnection>,
    mut tx: tokio::sync::watch::Sender<Option<Result<(), Error>>>,
    expires: tokio::time::Instant,
) {
    log::debug!("TEARDOWN {} starting", &*session_id);
    if tokio::time::timeout_at(
        expires,
        teardown_loop_forever(
            base_url,
            &*session_id,
            &options,
            requested_auth,
            conn,
            &mut tx,
        ),
    )
    .await
    .is_err()
    {
        log::debug!("TEARDOWN {} aborted on session expiration", &*session_id);
    }
    if let Some(ref session_group) = options.session_group {
        let seqnum = seqnum.expect("seqnum specified when session_group exists");
        let mut l = session_group.0.lock().unwrap();
        let i = l.sessions.iter().position(|s| s.seqnum == seqnum);
        match i {
            Some(i) => {
                l.sessions.swap_remove(i);
            }
            None => log::warn!("Unable to find session {:?} on TEARDOWN", &*session_id),
        }
    }

    let _ = tx.send(Some(Ok(())));
}

/// Attempts `TEARDOWN` in a loop until success; caller should bound by session expiry.
pub(super) async fn teardown_loop_forever(
    url: Url,
    session_id: &str,
    options: &SessionOptions,
    mut requested_auth: Option<digest_auth::WwwAuthenticateHeader>,
    mut conn: Option<RtspConnection>,
    tx: &mut tokio::sync::watch::Sender<Option<Result<(), Error>>>,
) {
    let mut req = rtsp_types::Request::builder(Method::Teardown, rtsp_types::Version::V1_0)
        .request_uri(url.clone())
        .header(rtsp_types::headers::SESSION, session_id.to_string())
        .build(Bytes::new());

    let attempt_deadline = tokio::time::sleep(EXISTING_CONN_TIMEOUT);
    tokio::pin!(attempt_deadline);
    if let Some(conn) = conn.take() {
        // Attempt first on existing connection. Besides being the most
        // efficient approach, this is the best for old live555 servers' stale
        // TCP sessions. Tearing them down before closing the connection means
        // they don't have a chance to mess up any other sockets.
        tokio::select! {
            biased;
            r = attempt(&mut req, &options, &mut requested_auth, conn) => {
                match r {
                    Ok(()) => {
                        log::debug!("TEARDOWN {} on existing conn succeeded.", session_id);
                        return
                    },
                    Err(e) => {
                        // Retry with a new connection, without waiting for the
                        // attempt deadline.
                        //
                        // A particularly likely case is when the session was
                        // dropped due to corrupt message. This attempt will
                        // inevitably fail reading the same corrupt message.
                        // It's worth trying anyway because the server may
                        // actually execute the TEARDOWN, even though we can't
                        // read the response.
                        //
                        // The first try with a fresh connection is likely
                        // to be more successful, and maybe will simply confirm
                        // the session is already destroyed. Do it soon.
                        //
                        // Also, don't update tx, so await_teardown() won't
                        // fail early. Let's at least do an attempt with a fresh
                        // connection first.
                        log::debug!("TEARDOWN {} on existing conn failed: {}", session_id, &e);
                    },
                }
            },
            _ = &mut attempt_deadline => log::debug!("TEARDOWN {} on existing conn timed out", session_id),
        }
    };

    // Now retry with a fresh connection each time, giving longer times to
    // subsequent attempts.
    let mut timeout = FRESH_CONN_INITIAL_TIMEOUT;
    for attempt_num in 1.. {
        attempt_deadline
            .as_mut()
            .reset(tokio::time::Instant::now() + timeout);
        let attempt = async {
            let conn = RtspConnection::connect(&url).await?;
            attempt(&mut req, &options, &mut requested_auth, conn).await
        };
        tokio::select! {
            biased;
            r = attempt => {
                match r {
                    Ok(()) => {
                        log::debug!("TEARDOWN {} fresh connection attempt {} succeeded.", session_id, attempt_num);
                        return
                    },
                    Err(e) => {
                        log::debug!("TEARDOWN {} fresh connection attempt {} failed: {}", session_id, attempt_num, &e);
                        let _ = tx.send(Some(Err(e)));

                        // Wait out the remaining time before trying again, to
                        // avoid going crazy when the server fails quickly.
                        attempt_deadline.as_mut().await;
                    },
                }
            },
            _ = &mut attempt_deadline => {
                log::debug!("TEARDOWN {} fresh connection attempt {} timed out", session_id, attempt_num);
                let _ = tx.send(Some(Err(wrap!(ErrorInt::Timeout))));
            },
        }
        timeout = std::cmp::min(timeout * 2, FRESH_CONN_MAX_TIMEOUT);
    }
}

/// Makes a single attempt on the supplied connection; caller is responsible for the timeout.
async fn attempt(
    req: &mut Request<Bytes>,
    options: &SessionOptions,
    requested_auth: &mut Option<digest_auth::WwwAuthenticateHeader>,
    mut conn: RtspConnection,
) -> Result<(), Error> {
    let e = match conn
        .send(ResponseMode::Teardown, &options, requested_auth, req)
        .await
    {
        Ok(_) => return Ok(()),
        Err(e) => e,
    };

    // Use a second match clause to look inside the Arc.
    match *e.0 {
        ErrorInt::RtspResponseError { status, .. }
            if status == rtsp_types::StatusCode::SessionNotFound =>
        {
            Ok(())
        }
        _ => Err(e),
    }
}
