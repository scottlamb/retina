// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::{str::FromStr as _, sync::Once};

static INIT_LOGGING: Once = Once::new();

// This is slightly different from `retina::testutil::init_logging()`:
// * it defaults to no logging so that fuzzing output is not polluted with log messages,
//   unless requested when drilling in.
// * it doesn't force `eprintln!()`, as fuzzing doesn't go through `libtest`.
pub fn init_logging() {
    INIT_LOGGING.call_once(|| {
        let h = mylog::Builder::new()
            .format(
                ::std::env::var("RUST_FORMAT")
                    .map_err(|_| ())
                    .and_then(|s| mylog::Format::from_str(&s))
                    .unwrap_or(mylog::Format::Google),
            )
            .spec(::std::env::var("RUST_LOG").as_deref().unwrap_or(""))
            .build();
        h.install().unwrap();
    })
}
