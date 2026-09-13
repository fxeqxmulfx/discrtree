//! discrtree — find a Lean declaration by shape, and lift it into a proof.
//!
//! The crate is layered, dependencies pointing inwards only:
//!
//! * [`domain`] — entities and rules. Pure: no I/O, no SQL, no JSON, no Lean.
//! * [`application`] — use cases, expressed against the ports in
//!   [`application::ports`]. Knows what `dt add` means, not where rows live.
//! * [`infrastructure`] — the adapters that implement those ports: SQLite,
//!   JSONL, `lake env lean`, `git`, the filesystem, `discrtree.toml`.
//! * [`interface`] — the `dt` command line and how results are rendered.
//!
//! The layering is what lets the whole of `domain` and `application` be tested
//! without a Lean toolchain, a database or a network.

pub mod application;
pub mod domain;
pub mod error;
pub mod infrastructure;
pub mod interface;

pub use error::{Error, Result};
