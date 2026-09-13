//! The `dt` command line: argument parsing, wiring the adapters to the use
//! cases, and rendering results. Nothing here decides anything.

pub mod cli;
pub mod render;
pub mod run;

pub use cli::Cli;
