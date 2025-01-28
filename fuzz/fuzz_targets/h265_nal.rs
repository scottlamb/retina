// Copyright (C) 2024 Scott Lamb <slamb@slamb.org>
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use libfuzzer_sys::fuzz_target;

use retina::codec::h265::nal;

fuzz_target!(|data: &[u8]| {
    let Ok((h, bits)) = nal::split(data) else {
        return;
    };

    match h.unit_type() {
        nal::UnitType::SpsNut => {
            let _ = nal::Sps::from_bits(bits);
        }
        nal::UnitType::PpsNut => {
            let _ = nal::Pps::from_bits(bits);
        }
        _ => {}
    }
});
