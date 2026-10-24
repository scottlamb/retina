// Copyright (C) The Retina Authors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! [`Error`], returned by the fallible public functions in [`crate::codec`].

use std::sync::Arc;

/// An error from the codec layer.
///
/// This is opaque; use [`Error::kind`] to classify it. Its
/// [`std::fmt::Display`] output describes the problem in detail.
///
/// Whether an error affects a whole stream or a single frame depends on the
/// function that returned it; see that function's documentation.
#[derive(Clone)]
pub struct Error(Box<ErrorInner>);

#[derive(Clone)]
struct ErrorInner {
    kind: ErrorKind,
    msg: String,
    source: Option<Arc<dyn std::error::Error + Send + Sync + 'static>>,
}

/// The kind of a [`codec::Error`](Error).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ErrorKind {
    /// Retina doesn't handle this media type, encoding, or parameter
    /// combination, possibly because a cargo feature is disabled.
    Unsupported,

    /// The supplied data or parameters are malformed: an `fmtp` attribute,
    /// a parameter set, a byte stream's NAL framing, a clock rate of zero.
    Invalid,
}

impl Error {
    /// Returns the kind of error.
    #[inline]
    pub fn kind(&self) -> ErrorKind {
        self.0.kind
    }

    pub(crate) fn new(kind: ErrorKind, msg: impl Into<String>) -> Self {
        Self(Box::new(ErrorInner {
            kind,
            msg: msg.into(),
            source: None,
        }))
    }

    /// Returns an [`ErrorKind::Invalid`] error with the given message.
    pub(crate) fn invalid(msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Invalid, msg)
    }

    /// Returns an [`ErrorKind::Unsupported`] error with the given message.
    pub(crate) fn unsupported(msg: impl Into<String>) -> Self {
        Self::new(ErrorKind::Unsupported, msg)
    }

    /// Sets the error's `source()`.
    ///
    /// The message should already describe the source, for consistency with
    /// other Retina errors.
    #[cfg_attr(not(feature = "h265"), allow(dead_code))]
    pub(crate) fn with_source(
        mut self,
        source: impl std::error::Error + Send + Sync + 'static,
    ) -> Self {
        self.0.source = Some(Arc::new(source));
        self
    }
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Error")
            .field("kind", &self.0.kind)
            .field("msg", &self.0.msg)
            .field("source", &self.0.source)
            .finish()
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0.msg)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.0
            .source
            .as_deref()
            .map(|s| s as &(dyn std::error::Error + 'static))
    }
}
