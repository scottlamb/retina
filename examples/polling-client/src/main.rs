// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Plays an RTSP stream without async, printing a line per frame.
//!
//! This drives Retina's sans-I/O [`SessionCore`] with plain non-blocking `std::net` sockets and a single `poll(2)`-style loop
//! (via the `polling` crate). One thread handles everything a session needs at
//! once: reading media and keepalive responses from the RTSP connection,
//! writing keepalives and receiver reports, reading UDP sockets, and timers.
//!
//! When done, it ends the session on the server as a dropped `Session` would,
//! via [`TeardownCore`]: first on the session's connection, then (if the
//! server is known to be buggy, or with UDP) on fresh connections.
//!
//! It's meant to be copied and adapted, e.g. to put several sessions on one
//! poller, or to substitute `mio`.

use std::io::{self, IoSlice, IoSliceMut, Read as _, Write as _};
use std::net::{SocketAddr, TcpStream, ToSocketAddrs as _};
use std::str::FromStr as _;
use std::time::{Duration, Instant};

use anyhow::{Context as _, Error, bail};
use clap::Parser;
use log::{debug, info, warn};
use polling::{Event, Events, Poller};
use retina::PacketContext;
use retina::buf::MarkBuf;
use retina::client::{
    ChannelType, Credentials, PlayOptions, PlayingItem, SessionCore, SessionEvent, SessionOptions,
    SetupTransport, TeardownAction, TeardownCore,
};
use retina::codec::{
    Accumulate, AudioFrameRef, AudioHandler, Depacketizer, Loss, MessageFrameRef, MessageHandler,
    VideoData, VideoFrameEnd, VideoFrameStart, VideoHandler,
};

/// How long to wait for each request before `PLAY`.
const REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

/// Datagrams can't be larger than this, so a UDP read needs at most this much
/// buffer space.
const MAX_DATAGRAM: usize = u16::MAX as usize;

#[derive(Parser)]
struct Opts {
    /// `rtsp://` URL to connect to.
    #[arg(long)]
    url: url::Url,

    /// Username to send if the server requires authentication.
    #[arg(long)]
    username: Option<String>,

    /// Password; requires username.
    #[arg(long, requires = "username")]
    password: Option<String>,

    /// Transport for RTP: `tcp` (interleaved) or `udp`.
    #[arg(long, default_value = "tcp")]
    transport: Transport,

    /// Stops (with a `TEARDOWN`) after this many seconds; by default, plays
    /// until the server ends the session.
    #[arg(long)]
    duration: Option<u64>,
}

#[derive(Copy, Clone, clap::ValueEnum)]
enum Transport {
    Tcp,
    Udp,
}

/// Poller key for the RTSP connection. UDP stream `i`'s RTP and RTCP sockets
/// use `1 + 2*i` and `2 + 2*i`.
const TCP_KEY: usize = 0;

/// A sans-I/O core with bytes to write to the RTSP connection.
trait Transmit {
    fn transmit_buf(&self) -> (&[u8], &[u8]);
    fn advance_transmit(&mut self, n: usize);
}

impl Transmit for SessionCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]) {
        SessionCore::transmit_buf(self)
    }
    fn advance_transmit(&mut self, n: usize) {
        SessionCore::advance_transmit(self, n)
    }
}

impl Transmit for TeardownCore {
    fn transmit_buf(&self) -> (&[u8], &[u8]) {
        TeardownCore::transmit_buf(self)
    }
    fn advance_transmit(&mut self, n: usize) {
        TeardownCore::advance_transmit(self, n)
    }
}

/// Connects to the host and port named in `url`.
///
/// Name resolution and connection setup are left blocking for simplicity;
/// the sans-I/O cores start once a connection is established.
fn connect_tcp(url: &url::Url, timeout: Duration) -> io::Result<TcpStream> {
    let host = url
        .host_str()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "URL has no host"))?;
    let port = url.port().unwrap_or(554);
    let mut last_err = None;
    for addr in (host, port).to_socket_addrs()? {
        match TcpStream::connect_timeout(&addr, timeout) {
            Ok(s) => return Ok(s),
            Err(e) => last_err = Some(e),
        }
    }
    Err(last_err.unwrap_or_else(|| {
        io::Error::new(
            io::ErrorKind::NotFound,
            format!("{host} resolved to no addresses"),
        )
    }))
}

/// The sockets of a session, registered with a poller.
struct Io {
    poller: Poller,
    events: Events,
    tcp: TcpStream,

    /// For each stream set up via UDP, its RTP and RTCP sockets.
    udp: Vec<Option<retina::UdpPair>>,
}

impl Io {
    /// Registers a newly established RTSP connection with a fresh poller.
    fn new(tcp: TcpStream) -> io::Result<Self> {
        tcp.set_nonblocking(true)?;
        tcp.set_nodelay(true)?;
        let poller = Poller::new()?;
        // SAFETY: `tcp` is deleted from the poller in `Drop`, before it's closed.
        unsafe { poller.add(&tcp, Event::readable(TCP_KEY))? };
        Ok(Self {
            poller,
            events: Events::new(),
            tcp,
            udp: Vec::new(),
        })
    }

    /// Binds a UDP socket pair for stream `stream_i`, returning its RTP port.
    fn bind_udp(&mut self, stream_i: usize) -> Result<u16, Error> {
        let pair = retina::UdpPair::for_ip(self.tcp.local_addr()?.ip())?;
        pair.rtp_socket.set_nonblocking(true)?;
        pair.rtcp_socket.set_nonblocking(true)?;
        let key = 1 + 2 * stream_i;
        // SAFETY: the sockets are deleted from the poller in `Drop`, before
        // they're closed.
        unsafe {
            self.poller.add(&pair.rtp_socket, Event::readable(key))?;
            self.poller
                .add(&pair.rtcp_socket, Event::readable(key + 1))?;
        }
        let port = pair.rtp_port;
        if self.udp.len() <= stream_i {
            self.udp.resize_with(stream_i + 1, || None);
        }
        self.udp[stream_i] = Some(pair);
        Ok(port)
    }

    fn udp_socket(&self, stream_i: usize, channel_type: ChannelType) -> &std::net::UdpSocket {
        let pair = self.udp[stream_i].as_ref().expect("stream is a UDP stream");
        match channel_type {
            ChannelType::Rtp => &pair.rtp_socket,
            ChannelType::Rtcp => &pair.rtcp_socket,
        }
    }

    /// Sends a packet on a UDP stream's socket, if it has room.
    fn send_udp(&self, stream_i: usize, channel_type: ChannelType, data: &[u8]) {
        if let Err(e) = self.udp_socket(stream_i, channel_type).send(data) {
            // A full socket buffer, or `ConnectionRefused` following an ICMP
            // error, isn't a reason to end the session.
            debug!("unable to send on stream {stream_i}'s {channel_type:?} socket: {e}");
        }
    }

    /// Writes as much of `core`'s transmit buffer as the socket will take.
    fn flush(&mut self, core: &mut impl Transmit) -> io::Result<()> {
        loop {
            let (first, second) = core.transmit_buf();
            if first.is_empty() {
                break;
            }
            match self
                .tcp
                .write_vectored(&[IoSlice::new(first), IoSlice::new(second)])
            {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => core.advance_transmit(n),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Reads whatever the RTSP connection has into `buf`, returning true if
    /// anything was read. Sets `eof` if the server closed the connection.
    fn read_tcp(&mut self, buf: &mut MarkBuf, eof: &mut bool) -> io::Result<bool> {
        let mut any = false;
        loop {
            let (first, second) = buf.spare_capacity(4096);
            let mut bufs = [IoSliceMut::new(first), IoSliceMut::new(second)];
            match self.tcp.read_vectored(&mut bufs) {
                Ok(0) => {
                    *eof = true;
                    return Ok(true);
                }
                Ok(n) => {
                    buf.advance_end(n);
                    any = true;
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => return Ok(any),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
    }

    /// Reads one datagram from a UDP stream's socket into `core`, returning
    /// true if one was read.
    fn read_udp(
        &self,
        core: &mut SessionCore,
        stream_i: usize,
        channel_type: ChannelType,
    ) -> Result<bool, retina::Error> {
        let socket = socket2::SockRef::from(self.udp_socket(stream_i, channel_type));
        let (first, second) = core.udp_buf(stream_i).spare_capacity(MAX_DATAGRAM);
        let first_len = first.len().min(MAX_DATAGRAM);
        let second_len = second.len().min(MAX_DATAGRAM - first_len);
        let mut bufs = [
            IoSliceMut::new(&mut first[..first_len]),
            IoSliceMut::new(&mut second[..second_len]),
        ];
        // On a connected datagram socket, a read is a `recv` of one datagram.
        match (&*socket).read_vectored(&mut bufs) {
            Ok(n) => {
                let n = u16::try_from(n).expect("datagram fits in u16");
                core.udp_received(stream_i, channel_type, n, Instant::now());
                Ok(true)
            }
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                ) =>
            {
                Ok(false)
            }
            Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => {
                // The hole-punching packets sent after `SETUP` can elicit an
                // ICMP 'destination unreachable' response, which becomes this.
                debug!("ignoring UDP connection refused error");
                Ok(false)
            }
            Err(e) => Err(core.udp_recv_error(stream_i, e)),
        }
    }

    /// Waits until a socket may be ready, or until `deadline`.
    ///
    /// Spurious wakeups are fine; the caller tries everything non-blockingly
    /// afterward.
    fn wait(&mut self, core: &impl Transmit, deadline: Instant) -> io::Result<()> {
        // `polling` registrations are one-shot; re-arm each time, asking for
        // writability only when there's something to write.
        let tcp_interest = if core.transmit_buf().0.is_empty() {
            Event::readable(TCP_KEY)
        } else {
            Event::all(TCP_KEY)
        };
        self.poller.modify(&self.tcp, tcp_interest)?;
        for (i, pair) in self.udp.iter().enumerate() {
            if let Some(pair) = pair {
                self.poller
                    .modify(&pair.rtp_socket, Event::readable(1 + 2 * i))?;
                self.poller
                    .modify(&pair.rtcp_socket, Event::readable(2 + 2 * i))?;
            }
        }
        self.events.clear();
        self.poller.wait_deadline(&mut self.events, deadline)?;
        Ok(())
    }
}

impl Drop for Io {
    fn drop(&mut self) {
        let _ = self.poller.delete(&self.tcp);
        for pair in self.udp.iter().flatten() {
            let _ = self.poller.delete(&pair.rtp_socket);
            let _ = self.poller.delete(&pair.rtcp_socket);
        }
    }
}

/// Does I/O until `core`'s outstanding request completes.
fn request(io: &mut Io, core: &mut SessionCore) -> Result<SessionEvent, Error> {
    let deadline = Instant::now() + REQUEST_TIMEOUT;
    loop {
        io.flush(core)?;
        if let Some(r) = core.poll_event(Instant::now()) {
            return Ok(r?);
        }
        let mut eof = false;
        match io.read_tcp(core.read_buf(), &mut eof) {
            Ok(true) => {
                if eof {
                    core.handle_eof();
                }
                continue;
            }
            Ok(false) => {}
            Err(e) => return Err(core.read_error(e, Instant::now()).into()),
        }
        if Instant::now() >= deadline {
            bail!("request timed out after {REQUEST_TIMEOUT:?}");
        }
        io.wait(core, deadline)?;
    }
}

/// Ends the session on the server, as [`SessionOptions::teardown`] says.
///
/// Returns `Ok(false)` if there was nothing to do.
fn teardown(io: Io, core: SessionCore) -> Result<bool, Error> {
    let Some(mut td) = core.into_teardown(Instant::now()) else {
        return Ok(false);
    };
    let mut io = Some(io);
    loop {
        let now = Instant::now();
        match td.poll(now) {
            TeardownAction::Io { deadline } => {
                let conn = io.as_mut().expect("Io follows a connection");
                if let Err(e) = conn.flush(&mut td) {
                    td.handle_io_error(e, Instant::now());
                    continue;
                }
                let mut eof = false;
                match conn.read_tcp(td.read_buf(), &mut eof) {
                    Ok(true) => {
                        if eof {
                            td.handle_eof();
                        }
                        continue;
                    }
                    Ok(false) => {}
                    Err(e) => {
                        td.handle_io_error(e, Instant::now());
                        continue;
                    }
                }
                conn.wait(&td, deadline)?;
            }
            TeardownAction::Connect { deadline } => {
                io = None;
                info!("TEARDOWN: connecting to {}", td.url());
                let timeout = deadline.saturating_duration_since(now);
                match connect_tcp(td.url(), timeout).and_then(Io::new) {
                    Ok(conn) => {
                        td.connected(
                            conn.tcp.local_addr()?,
                            conn.tcp.peer_addr()?,
                            Instant::now(),
                        );
                        io = Some(conn);
                    }
                    Err(e) => td.handle_io_error(e, Instant::now()),
                }
            }
            TeardownAction::Wait { until } => {
                io = None;
                std::thread::sleep(until.saturating_duration_since(now));
            }
            TeardownAction::Done => return Ok(true),
            _ => bail!("unexpected TeardownAction"),
        }
    }
}

/// Plays until `stop_at` or the server ends the session.
fn play(
    io: &mut Io,
    core: &mut SessionCore,
    streams: &mut [Option<Stream>],
    stop_at: Option<Instant>,
) -> Result<(), Error> {
    loop {
        let now = Instant::now();
        if stop_at.is_some_and(|t| now >= t) {
            info!("stopping after --duration");
            return Ok(());
        }

        // Handle everything already received.
        while let Some(item) = core.poll_item(now) {
            match item? {
                PlayingItem::Rtp(pkt) => {
                    let stream_id = pkt.stream_id();
                    let s = streams[stream_id]
                        .as_mut()
                        .expect("only set-up streams have packets");
                    let h = &mut Printer {
                        stream_id,
                        frame_len: &mut s.frame_len,
                    };
                    match &mut s.depacketizer {
                        Depacketizer::Video(d) => d.push(pkt.packet(), h),
                        Depacketizer::Audio(d) => d.push(pkt.packet(), h),
                        Depacketizer::Message(d) => d.push(pkt.packet(), h),
                        _ => {}
                    }
                }
                PlayingItem::Rtcp(pkt) => {
                    if let Some(t) = pkt.rtp_timestamp() {
                        debug!("stream {}: RTCP sender report at {t}", pkt.stream_id());
                    }
                }
                _ => {}
            }
        }
        if core.is_closed() {
            info!("server closed the connection");
            return Ok(());
        }

        // Send keepalives and receiver reports when due.
        let timeout = core.poll_timeout().expect("playing core has a timeout");
        if now >= timeout {
            core.handle_timeout(now)?;
        }
        io.flush(core)?;
        while let Some(t) = core.poll_transmit_udp() {
            io.send_udp(t.stream_i, t.channel_type, &t.data);
        }

        // Read whatever has arrived; if anything did, go handle it.
        let mut progress = false;
        let mut eof = false;
        match io.read_tcp(core.read_buf(), &mut eof) {
            Ok(read) => progress |= read,
            Err(e) => return Err(core.read_error(e, Instant::now()).into()),
        }
        if eof {
            core.handle_eof();
        }
        for stream_i in 0..io.udp.len() {
            if io.udp[stream_i].is_none() {
                continue;
            }
            // Prioritize RTCP; read a bounded number of datagrams so one busy
            // stream can't starve the others.
            for channel_type in [ChannelType::Rtcp, ChannelType::Rtp] {
                for _ in 0..64 {
                    if !io.read_udp(core, stream_i, channel_type)? {
                        break;
                    }
                    progress = true;
                }
            }
        }
        if progress {
            continue;
        }

        let mut deadline = core.poll_timeout().expect("playing core has a timeout");
        if let Some(t) = stop_at {
            deadline = deadline.min(t);
        }
        io.wait(core, deadline)?;
    }
}

/// A stream which has been set up.
struct Stream {
    depacketizer: Depacketizer<PacketContext>,

    /// The size so far of the video frame in progress.
    frame_len: usize,
}

/// Prints a line per frame of a single packet.
///
/// This uses the streaming depacketizer API, so it never accumulates whole
/// frames; it just totals their sizes.
struct Printer<'a> {
    stream_id: usize,
    frame_len: &'a mut usize,
}

impl VideoHandler<PacketContext> for Printer<'_> {
    fn frame_start(&mut self, frame_start: &mut VideoFrameStart<'_, PacketContext>) -> Accumulate {
        if frame_start.has_new_parameters()
            && let Some(p) = frame_start.parameters()
        {
            info!(
                "stream {}: {} {}x{}",
                self.stream_id,
                p.rfc6381_codec(),
                p.pixel_dimensions().0,
                p.pixel_dimensions().1
            );
        }
        *self.frame_len = 0;
        Accumulate::No
    }

    fn data(&mut self, data: &VideoData<'_>) {
        *self.frame_len += data.len();
    }

    fn frame_end(&mut self, frame_end: &mut VideoFrameEnd<'_, PacketContext>) {
        println!(
            "stream {}: video {} {:7} bytes{}",
            self.stream_id,
            frame_end.timestamp(),
            self.frame_len,
            if frame_end.is_random_access_point() {
                " (key)"
            } else {
                ""
            },
        );
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        warn!("stream {}: {:?}", self.stream_id, loss.reason());
    }
}

impl AudioHandler<PacketContext> for Printer<'_> {
    fn audio_frame(&mut self, frame: &AudioFrameRef<'_, PacketContext>) {
        println!(
            "stream {}: audio {} {:7} samples",
            self.stream_id,
            frame.timestamp(),
            frame.frame_length()
        );
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        warn!("stream {}: {:?}", self.stream_id, loss.reason());
    }
}

impl MessageHandler<PacketContext> for Printer<'_> {
    fn message_frame(&mut self, frame: &MessageFrameRef<'_, PacketContext>) {
        println!(
            "stream {}: message {} {:7} bytes",
            self.stream_id,
            frame.timestamp(),
            frame.data().len()
        );
    }

    fn loss(&mut self, loss: &Loss<'_, PacketContext>) {
        warn!("stream {}: {:?}", self.stream_id, loss.reason());
    }
}

fn run(opts: Opts) -> Result<(), Error> {
    let creds = opts.username.map(|username| Credentials {
        username,
        password: opts.password.unwrap_or_default(),
    });
    let tcp = connect_tcp(&opts.url, REQUEST_TIMEOUT)
        .with_context(|| format!("unable to connect to {}", opts.url))?;
    let mut io = Io::new(tcp)?;
    let local_addr: SocketAddr = io.tcp.local_addr()?;
    let mut core = SessionCore::new(
        local_addr,
        io.tcp.peer_addr()?,
        SessionOptions::default()
            .creds(creds)
            .user_agent("Retina polling-client example".to_owned()),
    );

    core.describe(opts.url.clone())?;
    request(&mut io, &mut core)?;

    // Set up every stream Retina can depacketize.
    let mut streams: Vec<Option<Stream>> = (0..core.streams().len()).map(|_| None).collect();
    for i in 0..core.streams().len() {
        let s = &core.streams()[i];
        let depacketizer = match s.new_depacketizer() {
            Ok(d) => d,
            Err(e) => {
                info!(
                    "skipping stream {i} ({}/{}): {e}",
                    s.media(),
                    s.encoding_name()
                );
                continue;
            }
        };
        info!(
            "setting up stream {i} ({}/{})",
            s.media(),
            s.encoding_name()
        );
        let transport = match opts.transport {
            Transport::Tcp => SetupTransport::Tcp,
            Transport::Udp => SetupTransport::Udp {
                client_rtp_port: io.bind_udp(i)?,
                options: Default::default(),
            },
        };
        core.setup(i, transport)?;
        if let SessionEvent::SetUp {
            udp_peer: Some(peer),
            ..
        } = request(&mut io, &mut core)?
        {
            let pair = io.udp[i].as_ref().expect("bound above");
            pair.rtp_socket.connect(peer)?;
            pair.rtcp_socket
                .connect(SocketAddr::new(peer.ip(), peer.port() + 1))?;
            while let Some(t) = core.poll_transmit_udp() {
                io.send_udp(t.stream_i, t.channel_type, &t.data);
            }
        }
        streams[i] = Some(Stream {
            depacketizer,
            frame_len: 0,
        });
    }
    if streams.iter().all(Option::is_none) {
        bail!("no streams Retina can depacketize");
    }

    core.play(PlayOptions::default())?;
    request(&mut io, &mut core)?;
    let stop_at = opts
        .duration
        .map(|secs| Instant::now() + Duration::from_secs(secs));
    let result = play(&mut io, &mut core, &mut streams, stop_at);
    if let Err(e) = &result {
        warn!("playing failed: {e}");
    }
    match teardown(io, core) {
        Ok(true) => info!("TEARDOWN done"),
        Ok(false) => {}
        Err(e) => warn!("TEARDOWN failed: {e}"),
    }
    result
}

fn main() {
    let h = mylog::Builder::new()
        .format(
            ::std::env::var("RUST_FORMAT")
                .map_err(|_| ())
                .and_then(|s| mylog::Format::from_str(&s))
                .unwrap_or(mylog::Format::Google),
        )
        .spec(::std::env::var("RUST_LOG").as_deref().unwrap_or("info"))
        .build();
    h.install().unwrap();
    if let Err(e) = run(Opts::parse()) {
        log::error!("Fatal: {}", chain(&e));
        std::process::exit(1);
    }
}

/// Formats an error with its causes.
fn chain(e: &Error) -> String {
    e.chain()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join("\ncaused by: ")
}
