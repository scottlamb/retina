// Copyright (C) 2024 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Common logic between H.264 and H.265.

/// `h264_reader::rbsp::BitRead` impl that *notes* extra trailing data rather than failing on it.
///
/// Some (Reolink) cameras appear to have a stray extra byte at the end. Follow the lead of most
/// other RTSP implementations in tolerating this.
#[derive(Debug)]
pub(super) struct TolerantBitReader<'a, R> {
    pub(super) inner: R,
    pub(super) has_extra_trailing_data: &'a mut bool,
}

impl<R: h264_reader::rbsp::BitRead> h264_reader::rbsp::BitRead for TolerantBitReader<'_, R> {
    fn read_ue(&mut self, name: &'static str) -> Result<u32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_ue(name)
    }

    fn read_se(&mut self, name: &'static str) -> Result<i32, h264_reader::rbsp::BitReaderError> {
        self.inner.read_se(name)
    }

    fn read_bool(&mut self, name: &'static str) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        self.inner.read_bool(name)
    }

    fn skip(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.skip(bit_count, name)
    }

    fn read<U: h264_reader::rbsp::Numeric>(
        &mut self,
        bit_count: u32,
        name: &'static str,
    ) -> Result<U, h264_reader::rbsp::BitReaderError> {
        self.inner.read(bit_count, name)
    }

    fn read_to<V: h264_reader::rbsp::Primitive>(
        &mut self,
        name: &'static str,
    ) -> Result<V, h264_reader::rbsp::BitReaderError> {
        self.inner.read_to(name)
    }

    fn has_more_rbsp_data(
        &mut self,
        name: &'static str,
    ) -> Result<bool, h264_reader::rbsp::BitReaderError> {
        self.inner.has_more_rbsp_data(name)
    }

    fn finish_rbsp(self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        match self.inner.finish_rbsp() {
            Ok(()) => Ok(()),
            Err(h264_reader::rbsp::BitReaderError::RemainingData) => {
                *self.has_extra_trailing_data = true;
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    fn finish_sei_payload(self) -> Result<(), h264_reader::rbsp::BitReaderError> {
        self.inner.finish_sei_payload()
    }
}
