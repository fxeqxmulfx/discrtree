//! Use cases. Each one knows what a command means and nothing about where rows
//! are stored, how Lean is invoked or how results are printed.

pub mod add;
pub mod deps;
pub mod find;
pub mod generated;
pub mod index;
pub mod ports;
pub mod rdeps;
pub mod ship;
pub mod show;
pub mod status;

pub use ports::{
    DeclRepo, DeclSink, DumpSpec, Elaborator, FetchSpec, ProjectWriter, SourceFiles, Vcs, Workspace,
};
