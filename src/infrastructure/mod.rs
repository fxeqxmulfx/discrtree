//! Adapters. Everything that knows about TOML, SQLite, JSON, `git` and
//! `lake env lean` lives here and nowhere else.

pub mod config;
pub mod git;
pub mod jsonl;
pub mod lake;
pub mod project;
pub mod revision;
pub mod sqlite;

pub use config::Config;
