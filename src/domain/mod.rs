//! Entities and rules. Nothing here reads a file, opens a database or knows
//! that Lean exists as a process.

pub mod closure;
pub mod decl;
pub mod lean_text;
pub mod name;
pub mod pattern;
pub mod query;
pub mod source;
pub mod vendor;

pub use decl::{ArgHead, Decl, DeclKind, Shape, Span};
pub use name::{DeclName, ModuleName};
pub use query::Query;
pub use source::{SourceId, SourceKind, SourceMeta};
