// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Power-of-two ring buffer for network I/O.

use crate::inputs::Split;
use crate::to_u64;

/// A power-of-two ring buffer.
///
/// Data is accessed as up to two slices (the ring's discontiguous halves).
/// This is simpler than maintaining a copy region for contiguous access
/// and sufficient when callers can work with split slices (e.g. the RTSP
/// parser via [`crate::inputs::Split`]).
///
/// `start` and `end` are monotonically increasing stream positions;
/// the index into `buf` is obtained by masking with `buf.len() - 1`.
///
/// ```text
/// Contiguous data (start_i < end_i):
///
///   0             start_i        end_i       buf.len()
///   |  free space  | === data === |  free space  |
///
/// Wrapped data (end_i <= start_i):
///
///   0        end_i          start_i          buf.len()
///   | = data = |  free space  | ==== data ==== |
/// ```
pub(crate) struct RingBuf {
    buf: Box<[u8]>,

    /// Stream position of the first valid byte.
    start: u64,

    /// Stream position one past the last valid byte.
    end: u64,
}

#[allow(dead_code)] // Some methods reserved for future steps.
impl RingBuf {
    /// Creates a new ring buffer with at least `capacity` bytes
    /// (rounded up to a power of two).
    pub fn new(capacity: usize) -> Self {
        let capacity = capacity.max(1).checked_next_power_of_two().unwrap();
        Self {
            buf: vec![0; capacity].into_boxed_slice(),
            start: 0,
            end: 0,
        }
    }

    #[inline]
    fn mask(&self) -> usize {
        self.buf.len() - 1
    }

    /// Stream position of the first valid byte.
    #[inline]
    pub fn start(&self) -> u64 {
        self.start
    }

    /// Stream position one past the last valid byte.
    #[inline]
    pub fn end(&self) -> u64 {
        self.end
    }

    /// Number of valid bytes in the buffer.
    #[inline]
    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Ring capacity (always a power of two).
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buf.len()
    }

    /// Free space available for writing without reallocation.
    #[inline]
    pub fn available(&self) -> usize {
        self.buf.len() - self.len()
    }

    /// Returns data at `[pos, pos+len)` as a [`Split`].
    ///
    /// # Panics
    ///
    /// Panics if the range is outside `[start, end)`.
    pub fn split(&self, pos: u64, len: usize) -> Split<'_> {
        assert!(
            pos >= self.start && pos + to_u64(len) <= self.end,
            "split({pos}, {len}) outside valid range [{}, {})",
            self.start,
            self.end,
        );
        let i = pos as usize & self.mask();
        let contiguous = self.buf.len() - i;
        if let Some(second_len) = len.checked_sub(contiguous) {
            Split::new(&self.buf[i..], &self.buf[..second_len])
        } else {
            Split::new(&self.buf[i..i + len], &[])
        }
    }

    /// Returns all buffered data as a [`Split`].
    pub fn data_split(&self) -> Split<'_> {
        if self.is_empty() {
            return Split::new(&[], &[]);
        }
        self.split(self.start, self.len())
    }

    /// Marks bytes before `pos` as consumed.
    ///
    /// # Panics
    ///
    /// Panics unless `start <= pos <= end`.
    pub fn advance_to(&mut self, pos: u64) {
        assert!(
            self.start <= pos && pos <= self.end,
            "advance_to({pos}): must be within [{}, {}]",
            self.start,
            self.end,
        );
        self.start = pos;
    }

    /// Returns the free space as up to two mutable slices.
    ///
    /// After writing `n` bytes into these slices (starting from the first),
    /// call [`advance_end`](Self::advance_end) to mark them as valid.
    ///
    /// Ensures at least `reserve` bytes of free space (growing if needed).
    pub fn spare_capacity(&mut self, reserve: usize) -> (&mut [u8], &mut [u8]) {
        self.reserve(reserve);
        if self.len() == self.buf.len() {
            // Full. `start_i == end_i` below, which is indistinguishable from
            // empty, so special-case it rather than returning the whole ring.
            return (&mut [], &mut []);
        }
        let mask = self.mask();
        let end_i = self.end as usize & mask;
        let start_i = self.start as usize & mask;

        if end_i < start_i {
            // Data wraps; free space is contiguous [end_i, start_i).
            (&mut self.buf[end_i..start_i], &mut [])
        } else {
            // Data is contiguous (or buffer is empty);
            // free space wraps: [end_i, buf.len()) and [0, start_i).
            let (head, tail) = self.buf.split_at_mut(end_i);
            (tail, &mut head[..start_i])
        }
    }

    /// Marks `n` additional bytes at the end as valid.
    ///
    /// # Panics
    ///
    /// Panics if `n > self.available()`.
    pub fn advance_end(&mut self, n: usize) {
        assert!(
            n <= self.available(),
            "advance_end({n}): only {} available",
            self.available(),
        );
        self.end += to_u64(n);
    }

    /// Appends `data` to the buffer, growing if necessary.
    #[cfg(test)]
    pub fn extend(&mut self, data: &[u8]) {
        let (s1, s2) = self.spare_capacity(data.len());
        let mid = data.len().min(s1.len());
        s1[..mid].copy_from_slice(&data[..mid]);
        s2[..data.len() - mid].copy_from_slice(&data[mid..]);
        self.advance_end(data.len());
    }

    /// Ensures capacity for at least `additional` more bytes.
    #[inline]
    fn reserve(&mut self, additional: usize) {
        if additional > self.available() {
            self.realloc(additional);
        }
    }

    #[cold]
    fn realloc(&mut self, additional: usize) {
        let data_len = self.len();
        let new_size = data_len
            .checked_add(additional)
            .and_then(usize::checked_next_power_of_two)
            .unwrap();
        debug_assert!(new_size > self.buf.len());
        let mut new_buf = vec![0u8; new_size].into_boxed_slice();

        if data_len > 0 {
            let (s1, s2) = self.split(self.start, data_len).slices();
            // `start`'s index within the new ring is `start & (new_size - 1)`,
            // which is *not* necessarily its index within the old ring: it
            // differs by whichever multiple of the old size `start` has wrapped
            // by. The data can therefore still wrap around the end of the new
            // ring, so copy each source half in up to two chunks. `data_len <=
            // new_size`, so this never overwrites what it just wrote.
            let mut i = self.start as usize & (new_size - 1);
            for src in [s1, s2] {
                let contiguous = new_size - i;
                if let Some(second_len) = src.len().checked_sub(contiguous) {
                    new_buf[i..].copy_from_slice(&src[..contiguous]);
                    new_buf[..second_len].copy_from_slice(&src[contiguous..]);
                    i = second_len;
                } else {
                    new_buf[i..i + src.len()].copy_from_slice(src);
                    i += src.len();
                }
            }
        }

        self.buf = new_buf;
    }
}

impl std::fmt::Debug for RingBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RingBuf")
            .field("start", &self.start)
            .field("end", &self.end)
            .field("capacity", &self.buf.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ring_basic() {
        let mut buf = RingBuf::new(8);
        assert_eq!(buf.capacity(), 8);
        assert!(buf.is_empty());

        buf.extend(b"hello");
        assert_eq!(buf.len(), 5);
        assert_eq!(buf.split(0, 5).slices(), (&b"hello"[..], &b""[..]));

        buf.advance_to(3);
        assert_eq!(buf.start(), 3);
        assert_eq!(buf.len(), 2);
        assert_eq!(buf.split(3, 2).slices(), (&b"lo"[..], &b""[..]));
    }

    #[test]
    fn ring_wrap() {
        let mut buf = RingBuf::new(8);
        buf.extend(b"abcdefgh");
        assert_eq!(buf.available(), 0);
        buf.advance_to(6);
        assert_eq!(buf.available(), 6);
        buf.extend(b"ijkl");
        assert_eq!(buf.len(), 6);
        assert_eq!(buf.split(6, 6).slices(), (&b"gh"[..], &b"ijkl"[..]));
    }

    #[test]
    fn ring_realloc() {
        let mut buf = RingBuf::new(4);
        buf.extend(b"ab");
        buf.advance_to(1);
        buf.extend(b"cde");
        assert_eq!(buf.len(), 4);
        assert_eq!(buf.available(), 0);

        buf.extend(b"fg");
        assert!(buf.capacity() >= 8);
        assert_eq!(buf.len(), 6);
        let (s1, s2) = buf.split(1, 6).slices();
        let mut all = Vec::new();
        all.extend_from_slice(s1);
        all.extend_from_slice(s2);
        assert_eq!(&all, b"bcdefg");
    }

    /// Regression test: a realloc while the data wraps the old ring *and*
    /// `start` has wrapped an odd number of times. `start`'s index within the
    /// new ring is then `old_index + old_size`, so the data still wraps in the
    /// new ring and a naive single-shot copy runs off the end.
    #[test]
    fn ring_realloc_wrapped_odd_parity() {
        let mut buf = RingBuf::new(8);
        buf.extend(b"abcdefgh");
        buf.advance_to(8);
        buf.extend(b"ABCDEFGH");
        buf.advance_to(11); // start=11: index 3, an odd number of wraps.
        buf.extend(b"xyz"); // start=11, end=19, len=8 (full, and wrapped).
        assert_eq!(buf.len(), 8);
        assert_eq!(buf.available(), 0);

        buf.extend(b"!"); // forces the realloc.
        assert_eq!(buf.len(), 9);
        let (s1, s2) = buf.split(11, 9).slices();
        let mut all = Vec::new();
        all.extend_from_slice(s1);
        all.extend_from_slice(s2);
        assert_eq!(&all, b"DEFGHxyz!");
    }

    /// Forces a realloc from every reachable `(start position, data length)`
    /// state, covering all start indices and wrap parities.
    #[test]
    fn ring_realloc_from_every_state() {
        const CAP: usize = 8;
        for start in 0..(4 * CAP as u64) {
            for len in 1..=CAP {
                let mut buf = RingBuf::new(CAP);

                // Churn `start` bytes through the ring without growing it, so
                // `start` lands at the intended index and number of wraps.
                let mut pos = 0u64;
                while pos < start {
                    let n = ((start - pos) as usize).min(CAP);
                    buf.extend(&vec![0u8; n]);
                    pos += n as u64;
                    buf.advance_to(pos);
                }
                assert_eq!(buf.capacity(), CAP);

                let data: Vec<u8> = (0..len).map(|i| (start as usize + i) as u8).collect();
                buf.extend(&data);
                let more: Vec<u8> = (0..CAP).map(|i| (i as u8) | 0x80).collect();
                buf.extend(&more); // forces the realloc
                assert!(buf.capacity() > CAP, "start={start} len={len}");

                let want: Vec<u8> = data.iter().chain(more.iter()).copied().collect();
                let (s1, s2) = buf.split(start, want.len()).slices();
                let got: Vec<u8> = s1.iter().chain(s2.iter()).copied().collect();
                assert_eq!(got, want, "start={start} len={len}");
            }
        }
    }

    /// `spare_capacity` must report no room when the ring is exactly full and
    /// nothing more was reserved; `start_i == end_i` is otherwise ambiguous
    /// with the empty case.
    #[test]
    fn spare_capacity_when_full() {
        let mut buf = RingBuf::new(8);
        buf.extend(b"abcdefgh");
        assert_eq!(buf.available(), 0);
        let (s1, s2) = buf.spare_capacity(0);
        assert_eq!((s1.len(), s2.len()), (0, 0));
    }

    #[test]
    fn spare_capacity_and_advance_end() {
        let mut buf = RingBuf::new(8);
        let (first, _) = buf.spare_capacity(5);
        first[..5].copy_from_slice(b"hello");
        buf.advance_end(5);
        assert_eq!(buf.len(), 5);
        assert_eq!(buf.data_split().slices(), (&b"hello"[..], &b""[..]));
    }

    #[test]
    fn data_split_empty() {
        let buf = RingBuf::new(8);
        assert_eq!(buf.data_split().slices(), (&b""[..], &b""[..]));
    }

    /// Verify `spare_capacity` returns enough space even when the buffer is
    /// empty but the internal cursor has wrapped past the end of the
    /// underlying array.
    #[test]
    fn spare_capacity_after_wrap() {
        let mut buf = RingBuf::new(8); // allocates 8 bytes

        // Fill the buffer almost completely, then consume everything,
        // leaving end near the end of the underlying array.
        let (s1, _) = buf.spare_capacity(7);
        s1[..7].copy_from_slice(b"abcdefg");
        buf.advance_end(7);
        buf.advance_to(buf.end()); // consume all data; buffer is now empty

        // end is at index 7. Requesting more bytes than the remaining
        // space (8 - 7 = 1) must still work because the buffer is empty
        // and the whole ring is available.
        let (s1, s2) = buf.spare_capacity(5);
        assert!(
            s1.len() + s2.len() >= 5,
            "s1.len()={}, s2.len()={}",
            s1.len(),
            s2.len(),
        );
    }
}
