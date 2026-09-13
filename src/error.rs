//! One error type for the whole binary. Every failure ends up as a message the
//! user reads in a terminal, so there is nothing to gain from a richer type.

use std::fmt;

#[derive(Debug)]
pub struct Error(String);

pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    pub fn new(msg: impl Into<String>) -> Self {
        Error(msg.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

macro_rules! from_error {
    ($t:ty, $ctx:expr) => {
        impl From<$t> for Error {
            fn from(e: $t) -> Self {
                Error(format!("{}: {e}", $ctx))
            }
        }
    };
}

from_error!(std::io::Error, "io");
from_error!(serde_json::Error, "json");
from_error!(toml::de::Error, "config");
from_error!(rusqlite::Error, "sqlite");

/// `bail!("...")` — the only control flow this crate needs on top of `?`.
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::error::Error::new(format!($($arg)*)))
    };
}

pub(crate) use bail;
