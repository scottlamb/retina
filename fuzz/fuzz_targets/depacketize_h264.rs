// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

#![no_main]
use libfuzzer_sys::{Corpus, fuzz_target};
use retina_fuzz::h26x::{Codec, Pkt};

fuzz_target!(|pkts: Vec<Pkt<'_>>| -> Corpus { retina_fuzz::h26x::run(Codec::H264, pkts) });
