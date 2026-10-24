// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`UdpPair`].

use log::trace;
use rand::Rng;
use std::net::{IpAddr, SocketAddr, UdpSocket};
use std::ops::Range;

/// A pair of local UDP sockets used for RTP and RTCP transmission.
///
/// The RTP port is always even, and the RTCP port is always the following (odd) integer.
///
/// [`client::Session`](crate::client::Session) binds these itself; callers of
/// [`client::SessionCore`](crate::client::SessionCore) may use this for
/// [`client::SetupTransport::Udp`](crate::client::SetupTransport::Udp).
#[derive(Debug)]
#[non_exhaustive]
pub struct UdpPair {
    pub rtp_port: u16,
    pub rtp_socket: UdpSocket,
    pub rtcp_socket: UdpSocket,
}

impl UdpPair {
    /// Binds a pair of sockets on `ip_addr`, at random ports.
    ///
    /// `ip_addr` should be the RTSP connection's local address.
    pub fn for_ip(ip_addr: IpAddr) -> Result<Self, std::io::Error> {
        const MAX_TRIES: usize = 10;
        const ALLOWED_RTP_RANGE: Range<u16> = 5000..65000; // stolen from ffmpeg's defaults.
        let mut rng = rand::thread_rng();
        for i in 0..MAX_TRIES {
            let rtp_port = rng.gen_range(ALLOWED_RTP_RANGE) & !0b1;
            debug_assert!(ALLOWED_RTP_RANGE.contains(&rtp_port));
            let rtp_addr = SocketAddr::new(ip_addr, rtp_port);
            let rtp_socket = match UdpSocket::bind(rtp_addr) {
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                    trace!(
                        "Try {}/{}: unable to bind RTP addr {:?}",
                        i, MAX_TRIES, rtp_addr
                    );
                    continue;
                }
                Err(e) => return Err(e),
            };
            let rtcp_addr = SocketAddr::new(ip_addr, rtp_port + 1);
            let rtcp_socket = match UdpSocket::bind(rtcp_addr) {
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
                    trace!(
                        "Try {}/{}: unable to bind RTCP addr {:?}",
                        i, MAX_TRIES, rtcp_addr
                    );
                    continue;
                }
                Err(e) => return Err(e),
            };
            return Ok(Self {
                rtp_port,
                rtp_socket,
                rtcp_socket,
            });
        }
        Err(std::io::Error::new(
            std::io::ErrorKind::AddrInUse,
            format!(
                "Unable to find even/odd pair in {}:{}..{} after {} tries",
                ip_addr, ALLOWED_RTP_RANGE.start, ALLOWED_RTP_RANGE.end, MAX_TRIES
            ),
        ))
    }
}

#[cfg(test)]
mod test {
    use std::net::Ipv4Addr;

    use super::*;

    #[test]
    fn local_udp_pair() {
        // Just test that it succeeds.
        UdpPair::for_ip(IpAddr::V4(Ipv4Addr::LOCALHOST)).unwrap();
    }
}
