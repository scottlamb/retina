// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Bytes queued for a sans-I/O core's RTSP connection; see [`TransmitBuf`].

use std::collections::VecDeque;

/// Bytes queued to write to an RTSP connection, owned by a sans-I/O core.
///
/// The driver writes from [`TransmitBuf::slices`] (ideally via vectored I/O)
/// and reports progress via [`TransmitBuf::advance`], so the core can retain
/// whatever wasn't written without copying or reallocating.
#[derive(Default)]
pub(crate) struct TransmitBuf {
    buf: VecDeque<u8>,

    /// The total number of bytes passed to [`TransmitBuf::advance`].
    written: u64,
}

impl TransmitBuf {
    /// Returns the bytes not yet written, in order.
    ///
    /// The first slice is empty iff there's nothing to write.
    pub(crate) fn slices(&self) -> (&[u8], &[u8]) {
        match self.buf.as_slices() {
            ([], b) => (b, &[]),
            s => s,
        }
    }

    /// Notes that the first `n` bytes of [`TransmitBuf::slices`] were written.
    ///
    /// # Panics
    ///
    /// If `n` exceeds the bytes available.
    pub(crate) fn advance(&mut self, n: usize) {
        assert!(
            n <= self.buf.len(),
            "advance({n}) exceeds the {} bytes queued",
            self.buf.len()
        );
        self.buf.drain(..n);
        self.written += n as u64;
    }

    /// Returns the total number of bytes written.
    pub(crate) fn written(&self) -> u64 {
        self.written
    }

    /// Returns the value [`TransmitBuf::written`] will have once everything
    /// queued so far has been written.
    pub(crate) fn queued_end(&self) -> u64 {
        self.written + self.buf.len() as u64
    }
}

impl std::io::Write for TransmitBuf {
    fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
        self.buf.write(data)
    }

    fn write_all(&mut self, data: &[u8]) -> std::io::Result<()> {
        self.buf.write_all(data)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write as _;

    use super::TransmitBuf;

    #[test]
    fn wraps() {
        let mut t = TransmitBuf::default();
        assert_eq!(t.slices(), (&[][..], &[][..]));
        t.write_all(b"abcd").unwrap();
        t.advance(3);
        let cap = t.buf.capacity();
        t.write_all(&vec![b'x'; cap - 1]).unwrap(); // fills to capacity, wrapping.
        assert_eq!(t.buf.capacity(), cap);
        let (a, b) = t.slices();
        assert!(!a.is_empty());
        assert_eq!([a, b].concat(), [&b"d"[..], &vec![b'x'; cap - 1]].concat());
        let n = a.len();
        assert_eq!(t.queued_end(), 3 + cap as u64);
        t.advance(n);
        assert_eq!(t.written(), 3 + n as u64);
        let (a, b) = t.slices();
        assert_eq!((a.len() + b.len()) as u64, t.queued_end() - t.written());
        assert!(b.is_empty());
    }
}
