use super::{VideoFrame, VideoParameters};
use crate::{rtp::ReceivedPacket, Error};
use bytes::Bytes;

#[derive(Debug)]
pub struct Depacketizer {
    pieces: Vec<Bytes>,
    pending: Option<VideoFrame>,
    parameters: Option<VideoParameters>,
}

impl Depacketizer {
    pub fn new() -> Self {
        Depacketizer {
            pieces: Vec::new(),
            pending: None,
            parameters: None,
        }
    }

    pub fn push(&mut self, packet: ReceivedPacket) -> Result<(), String> {
        // Push shouldn't be called until pull is exhausted.
        if let Some(p) = self.pending.as_ref() {
            panic!("push with data already pending: {p:?}");
        }

        // Extract the JPEG payload from the packet.
        let payload = packet.payload();

        // Process the payload according to RFC 2435.
        // RFC 2435 JPEG payload parsing
        let mut offset = 0;
        let mut quant = 0;
        let mut type_specific = 0;
        let mut width = 0;
        let mut height = 0;

        if payload.len() > 8 {
            offset = ((payload[1] as u16) << 8) | payload[0] as u16;
            type_specific = payload[2];
            quant = payload[3];
            width = payload[4] * 8;
            height = payload[5] * 8;
        }

        // Check if there is a quantization table
        if quant > 127 {
            let q_len = ((payload[7] as u16) << 8) | payload[6] as u16;
            // Skip the quantization table
            offset += q_len as u16;
        }

        // The remaining payload is the JPEG scan data
        let jpeg_scan_data = &payload[offset as usize..];

        // Store the JPEG scan data in pieces
        self.pieces.push(Bytes::copy_from_slice(jpeg_scan_data));

        // Check if we have all pieces of our frame
        // This is a placeholder condition, replace with actual condition
        if packet.mark() && !self.pieces.is_empty() {
            // If we have all pieces, store the completed frame in pending

            let data = self.pieces.concat();

            self.pending = Some(VideoFrame {
                start_ctx: *packet.ctx(),
                end_ctx: *packet.ctx(),
                has_new_parameters: false,
                loss: 0,
                timestamp: packet.timestamp(),
                stream_id: packet.stream_id(),
                is_random_access_point: false,
                is_disposable: false,
                data,
            });

            self.pieces.clear();
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
