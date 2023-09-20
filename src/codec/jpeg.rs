// Copyright (C) 2023 Niclas Olmenius
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [JPEG](https://www.itu.int/rec/T-REC-T.81-199209-I/en)-encoded video.

use bytes::{Buf, Bytes};

use crate::{rtp::ReceivedPacket, PacketContext, Timestamp};

use super::{VideoFrame, VideoParameters};

#[rustfmt::skip]
const ZIGZAG : [usize; 64] = [
    0, 1, 8, 16, 9, 2, 3, 10,
    17, 24, 32, 25, 18, 11, 4, 5,
    12, 19, 26, 33, 40, 48, 41, 34,
    27, 20, 13, 6, 7, 14, 21, 28,
    35, 42, 49, 56, 57, 50, 43, 36,
    29, 22, 15, 23, 30, 37, 44, 51,
    58, 59, 52, 45, 38, 31, 39, 46,
    53, 60, 61, 54, 47, 55, 62, 63
];

// The following constants and functions are ported from the reference
// C code in RFC 2435 Appendix A and B.

// Appendix A. from RFC 2435

/// Table K.1 from JPEG spec.
#[rustfmt::skip]
const JPEG_LUMA_QUANTIZER: [i32; 8 * 8] = [
    16, 11, 10, 16, 24, 40, 51, 61,
    12, 12, 14, 19, 26, 58, 60, 55,
    14, 13, 16, 24, 40, 57, 69, 56,
    14, 17, 22, 29, 51, 87, 80, 62,
    18, 22, 37, 56, 68, 109, 103, 77,
    24, 35, 55, 64, 81, 104, 113, 92,
    49, 64, 78, 87, 103, 121, 120, 101,
    72, 92, 95, 98, 112, 100, 103, 99,
];

/// Table K.2 from JPEG spec.
#[rustfmt::skip]
const JPEG_CHROMA_QUANTIZER: [i32; 8 * 8] = [
    17, 18, 24, 47, 99, 99, 99, 99,
    18, 21, 26, 66, 99, 99, 99, 99,
    24, 26, 56, 99, 99, 99, 99, 99,
    47, 66, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99,
    99, 99, 99, 99, 99, 99, 99, 99,
];

/// Calculate luma and chroma quantizer tables based on the given quality factor.
fn make_tables(q: i32) -> [u8; 128] {
    let factor = q.clamp(1, 99);
    let q = if factor < 50 {
        5000 / factor
    } else {
        200 - factor * 2
    };

    let mut qtable = [0u8; 128];
    for i in 0..64 {
        let lq = (JPEG_LUMA_QUANTIZER[ZIGZAG[i]] * q + 50) / 100;
        let cq = (JPEG_CHROMA_QUANTIZER[ZIGZAG[i]] * q + 50) / 100;

        /* Limit the quantizers to 1 <= q <= 255 */
        qtable[i] = lq.clamp(1, 255) as u8;
        qtable[i + 64] = cq.clamp(1, 255) as u8;
    }

    qtable
}

// End of Appendix A.

// Appendix B. from RFC 2435

const LUM_DC_CODELENS: [u8; 16] = [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0];
const LUM_DC_SYMBOLS: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
const LUM_AC_CODELENS: [u8; 16] = [0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 0x7d];

#[rustfmt::skip]
const LUM_AC_SYMBOLS: [u8; 162] = [
    0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12,
    0x21, 0x31, 0x41, 0x06, 0x13, 0x51, 0x61, 0x07,
    0x22, 0x71, 0x14, 0x32, 0x81, 0x91, 0xa1, 0x08,
    0x23, 0x42, 0xb1, 0xc1, 0x15, 0x52, 0xd1, 0xf0,
    0x24, 0x33, 0x62, 0x72, 0x82, 0x09, 0x0a, 0x16,
    0x17, 0x18, 0x19, 0x1a, 0x25, 0x26, 0x27, 0x28,
    0x29, 0x2a, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
    0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,
    0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,
    0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,
    0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,
    0x7a, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89,
    0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98,
    0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
    0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6,
    0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3, 0xc4, 0xc5,
    0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4,
    0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xe1, 0xe2,
    0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea,
    0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8,
    0xf9, 0xfa
];

const CHM_DC_CODELENS: [u8; 16] = [0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0];
const CHM_DC_SYMBOLS: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
const CHM_AC_CODELENS: [u8; 16] = [0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 0x77];

#[rustfmt::skip]
const CHM_AC_SYMBOLS: [u8; 162] = [
    0x00, 0x01, 0x02, 0x03, 0x11, 0x04, 0x05, 0x21,
    0x31, 0x06, 0x12, 0x41, 0x51, 0x07, 0x61, 0x71,
    0x13, 0x22, 0x32, 0x81, 0x08, 0x14, 0x42, 0x91,
    0xa1, 0xb1, 0xc1, 0x09, 0x23, 0x33, 0x52, 0xf0,
    0x15, 0x62, 0x72, 0xd1, 0x0a, 0x16, 0x24, 0x34,
    0xe1, 0x25, 0xf1, 0x17, 0x18, 0x19, 0x1a, 0x26,
    0x27, 0x28, 0x29, 0x2a, 0x35, 0x36, 0x37, 0x38,
    0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,
    0x49, 0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
    0x59, 0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,
    0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,
    0x79, 0x7a, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96,
    0x97, 0x98, 0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5,
    0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4,
    0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3,
    0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2,
    0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda,
    0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9,
    0xea, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8,
    0xf9, 0xfa
];

fn make_quant_header(p: &mut Vec<u8>, qt: &[u8], table_no: u8) {
    assert!(qt.len() < (u8::MAX - 3) as usize);

    p.push(0xff);
    p.push(0xdb); // DQT
    p.push(0); // length msb
    p.push(qt.len() as u8 + 3); // length lsb
    p.push(table_no);
    p.extend_from_slice(qt);
}

fn make_huffman_header(
    p: &mut Vec<u8>,
    codelens: &[u8],
    symbols: &[u8],
    table_no: u8,
    table_class: u8,
) {
    p.push(0xff);
    p.push(0xc4); // DHT
    p.push(0); // length msb
    p.push((3 + codelens.len() + symbols.len()) as u8); // length lsb
    p.push((table_class << 4) | table_no);
    p.extend_from_slice(codelens);
    p.extend_from_slice(symbols);
}

fn make_dri_header(p: &mut Vec<u8>, dri: u16) {
    p.push(0xff);
    p.push(0xdd); // DRI
    p.push(0x0); // length msb
    p.push(4); // length lsb
    p.push((dri >> 8) as u8); // dri msb
    p.push((dri & 0xff) as u8); // dri lsb
}

fn make_headers(
    p: &mut Vec<u8>,
    image_type: u8,
    width: u16,
    height: u16,
    mut qtable: Bytes,
    precision: u8,
    dri: u16,
) -> Result<(), String> {
    p.push(0xff);
    p.push(0xd8); // SOI

    let size = if (precision & 1) > 0 { 128 } else { 64 };
    if qtable.remaining() < size {
        return Err("Qtable too small".to_string());
    }
    make_quant_header(p, &qtable[..size], 0);
    qtable.advance(size);

    let size = if (precision & 2) > 0 { 128 } else { 64 };
    if qtable.remaining() < size {
        return Err("Qtable too small".to_string());
    }
    make_quant_header(p, &qtable[..size], 1);
    qtable.advance(size);

    if dri != 0 {
        make_dri_header(p, dri);
    }

    p.push(0xff);
    p.push(0xc0); // SOF
    p.push(0); // length msb
    p.push(17); // length lsb
    p.push(8); // 8-bit precision
    p.push((height >> 8) as u8); // height msb
    p.push(height as u8); // height lsb
    p.push((width >> 8) as u8); // width msb
    p.push(width as u8); // width lsb
    p.push(3); // number of components

    p.push(0); // comp 0
    if (image_type & 0x3f) == 0 {
        p.push(0x21); // hsamp = 2, vsamp = 1
    } else {
        p.push(0x22); // hsamp = 2, vsamp = 2
    }
    p.push(0); // quant table 0

    p.push(1); // comp 1
    p.push(0x11); // hsamp = 1, vsamp = 1
    p.push(1); // quant table 1

    p.push(2); // comp 2
    p.push(0x11); // hsamp = 1, vsamp = 1
    p.push(1); // quant table 1

    make_huffman_header(p, &LUM_DC_CODELENS, &LUM_DC_SYMBOLS, 0, 0);
    make_huffman_header(p, &LUM_AC_CODELENS, &LUM_AC_SYMBOLS, 0, 1);
    make_huffman_header(p, &CHM_DC_CODELENS, &CHM_DC_SYMBOLS, 1, 0);
    make_huffman_header(p, &CHM_AC_CODELENS, &CHM_AC_SYMBOLS, 1, 1);

    p.push(0xff);
    p.push(0xda); // SOS
    p.push(0); // length msb
    p.push(12); // length lsb
    p.push(3); // 3 components

    p.push(0); // comp 0
    p.push(0); // huffman table 0

    p.push(1); // comp 1
    p.push(0x11); // huffman table 1

    p.push(2); // comp 2
    p.push(0x11); // huffman table 1

    p.push(0); // first DCT coeff
    p.push(63); // last DCT coeff
    p.push(0); // successive approx.

    Ok(())
}

// End of Appendix B.

#[derive(Debug)]
struct JpegFrameMetadata {
    start_ctx: PacketContext,
    timestamp: Timestamp,
    parameters: Option<VideoParameters>,
}

/// A [super::Depacketizer] implementation which combines fragmented RTP/JPEG
/// into complete image frames as specified in [RFC
/// 2435](https://www.rfc-editor.org/rfc/rfc2435.txt).
#[derive(Debug)]
pub struct Depacketizer {
    /// Holds metadata for the current frame.
    metadata: Option<JpegFrameMetadata>,

    /// Backing storage to the assembled frame.
    data: Vec<u8>,

    /// Cached quantization tables.
    qtables: Vec<Option<Bytes>>,

    /// A complete video frame ready for pull.
    pending: Option<VideoFrame>,

    parameters: Option<VideoParameters>,
}

impl Depacketizer {
    pub fn new() -> Self {
        Depacketizer {
            metadata: None,
            data: Vec::new(),
            pending: None,
            qtables: vec![None; 255],
            parameters: None,
        }
    }

    pub(super) fn push(&mut self, pkt: ReceivedPacket) -> Result<(), String> {
        if let Some(p) = self.pending.as_ref() {
            panic!("push with data already pending: {p:?}");
        }

        if pkt.payload().len() < 8 {
            return Err("Too short RTP/JPEG packet".to_string());
        }

        let ctx = *pkt.ctx();
        let loss = pkt.loss();
        let stream_id = pkt.stream_id();
        let timestamp = pkt.timestamp();
        let last_packet_in_frame = pkt.mark();

        let mut payload = pkt.into_payload_bytes();

        //  0                   1                   2                   3
        //  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
        // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
        // | Type-specific |              Fragment Offset                  |
        // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
        // |      Type     |       Q       |     Width     |     Height    |
        // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
        let frag_offset = u32::from_be_bytes([0, payload[1], payload[2], payload[3]]);
        let type_specific = payload[4];
        let q = payload[5];
        let width = payload[6] as u16 * 8;
        let height = payload[7] as u16 * 8;

        let length;
        let mut dri: u16 = 0;
        let mut precision;
        let mut qtable;

        if frag_offset == 0 && self.metadata.is_some() {
            let _ = self.metadata.take();
            self.data.clear();

            return Err("Got new frame while frame is in progress".to_string());
        }

        payload.advance(8);

        if type_specific > 63 {
            if payload.remaining() < 4 {
                return Err("Too short RTP/JPEG packet".to_string());
            }

            //  0                   1                   2                   3
            //  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
            // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
            // |       Restart Interval        |F|L|       Restart Count       |
            // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
            dri = (payload[0] as u16) << 8 | payload[1] as u16;

            payload.advance(4);
        }

        if q >= 128 && frag_offset == 0 {
            if payload.len() < 4 {
                return Err("Too short RTP/JPEG packet".to_string());
            }

            //  0                   1                   2                   3
            //  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
            // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
            // |      MBZ      |   Precision   |             Length            |
            // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
            // |                    Quantization Table Data                    |
            // |                              ...                              |
            // +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+

            precision = payload[1];
            length = (payload[2] as u16) << 8 | payload[3] as u16;

            if q == 255 && length == 0 {
                return Err("Invalid RTP/JPEG packet. Quantization tables not found".to_string());
            }

            payload.advance(4);

            if length as usize > payload.len() {
                return Err(format!(
                    "Invalid RTP/JPEG packet. Length {length} larger than payload {}",
                    payload.len()
                ));
            }

            if length > 0 {
                qtable = Some(payload.clone());
            } else {
                qtable = self.qtables[q as usize].clone();
            }

            payload.advance(length as usize);
        } else {
            length = 0;
            qtable = None;
            precision = 0;
        }

        if frag_offset == 0 {
            if length == 0 {
                if q < 128 {
                    qtable = self.qtables[q as usize].clone();

                    if qtable.is_none() {
                        let table = Bytes::copy_from_slice(&make_tables(q as i32));
                        self.qtables[q as usize].replace(table);

                        qtable = self.qtables[q as usize].clone();
                    }

                    precision = 0;
                } else if qtable.is_none() {
                    return Err("Invalid RTP/JPEG packet. Missing quantization tables".to_string());
                }
            }

            match qtable {
                Some(qtable) => {
                    self.data.clear();

                    make_headers(
                        &mut self.data,
                        type_specific,
                        width,
                        height,
                        qtable,
                        precision,
                        dri,
                    )?;

                    self.metadata.replace(JpegFrameMetadata {
                        start_ctx: ctx,
                        timestamp,
                        parameters: Some(VideoParameters {
                            pixel_dimensions: (width as u32, height as u32),
                            rfc6381_codec: "".to_string(), // RFC 6381 is not applicable to MJPEG
                            pixel_aspect_ratio: None,
                            frame_rate: None,
                            extra_data: Bytes::new(),
                        }),
                    });
                }
                None => {
                    return Err("Invalid RTP/JPEG packet. Missing quantization tables".to_string());
                }
            }
        }

        let Some(metadata) = &self.metadata else {
            return Err("Invalid RTP/JPEG packet. Missing start packet".to_string());
        };

        if metadata.timestamp != timestamp {
            return Err("RTP timestamps don't match".to_string());
        }

        self.data.extend_from_slice(&payload);

        if last_packet_in_frame {
            if self.data.len() < 2 {
                return Ok(());
            }

            // Adding EOI marker if necessary.
            let end = &self.data[self.data.len() - 2..];
            if end[0] != 0xff && end[1] != 0xd9 {
                self.data.extend_from_slice(&[0xff, 0xd9]);
            }

            let has_new_parameters = self.parameters != metadata.parameters;

            self.pending = Some(VideoFrame {
                start_ctx: metadata.start_ctx,
                end_ctx: ctx,
                has_new_parameters,
                loss,
                timestamp,
                stream_id,
                is_random_access_point: false,
                is_disposable: false,
                data: std::mem::take(&mut self.data),
            });

            let metadata = self.metadata.take();
            if let Some(metadata) = metadata {
                if has_new_parameters {
                    self.parameters = metadata.parameters;
                }
            }
        }

        Ok(())
    }

    pub(super) fn pull(&mut self) -> Option<super::CodecItem> {
        self.pending.take().map(super::CodecItem::VideoFrame)
    }

    pub(super) fn parameters(&self) -> Option<super::ParametersRef> {
        self.parameters.as_ref().map(super::ParametersRef::Video)
    }
}

impl Default for Depacketizer {
    fn default() -> Self {
        Self::new()
    }
}
