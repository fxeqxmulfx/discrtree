//! The boundary. Every use case is written against these traits, and every one
//! of them has a test double in `tests/`.

use crate::domain::decl::Decl;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::query::Query;
use crate::domain::source::{SourceId, SourceMeta, Sources};
use crate::error::Result;
use std::path::{Path, PathBuf};

/// Reading the index.
pub trait DeclRepo {
    fn get(&self, name: &DeclName) -> Result<Option<Decl>>;
    fn find(&self, query: &Query) -> Result<Vec<Decl>>;
    /// Resolve many names at once. Separate from `get` because the closure walk
    /// asks for thousands and a per-name round trip dominates the run.
    fn get_many(&self, names: &[DeclName]) -> Result<Vec<Decl>>;
    /// Declarations per source, for `dt status`.
    fn counts(&self) -> Result<Vec<(SourceId, usize)>>;
    /// Names that exist at all, for turning scanned identifiers into
    /// dependencies.
    fn contains(&self, name: &DeclName) -> Result<bool> {
        Ok(self.get(name)?.is_some())
    }
}

/// Writing the index.
pub trait DeclSink {
    fn put(&mut self, decls: &[Decl]) -> Result<()>;
    /// Called once when every row is in: the moment to build the text index.
    fn finish(&mut self) -> Result<()>;
}

/// Reading the corpora on disk.
pub trait SourceFiles {
    /// The text of one module of one source.
    fn read_module(&self, source: &SourceId, module: &ModuleName) -> Result<String>;
    /// Every `.lean` file of a source, as (module, path).
    fn list_modules(&self, source: &SourceId) -> Result<Vec<(ModuleName, PathBuf)>>;
    /// Where the source lives, for error messages.
    fn location(&self, source: &SourceId) -> PathBuf;
}

/// What a dump needs to know. Phase 1 is Lean because only the elaborator can
/// read `.olean`; this is the whole interface to it.
#[derive(Debug, Clone)]
pub struct DumpSpec {
    pub source: SourceId,
    /// The module the dump imports, e.g. `Mathlib`.
    pub root: String,
    /// Module prefixes to keep.
    pub modules: Vec<String>,
    pub out: PathBuf,
    /// Whether to read proof terms. Off gives a much faster dump with
    /// dependencies missing.
    pub with_deps: bool,
}

/// Running Lean over a compiled source.
pub trait Elaborator {
    fn dump(&self, spec: &DumpSpec) -> Result<PathBuf>;
}

#[derive(Debug, Clone)]
pub struct FetchSpec {
    pub source: SourceId,
    pub url: String,
    pub rev: String,
    /// Sparse-checkout directories. Empty means everything.
    pub sparse: Vec<String>,
    pub into: PathBuf,
}

/// Bringing a text corpus onto the machine.
pub trait Vcs {
    fn fetch(&self, spec: &FetchSpec) -> Result<PathBuf>;
    /// The revision actually checked out, for the provenance header.
    fn revision(&self, path: &Path) -> Result<Option<String>>;
}

/// Writing into the project. The only port that touches `src/`.
pub trait ProjectWriter {
    /// Create a module, failing rather than overwriting unless `force`.
    fn write_module(&mut self, path: &Path, contents: &str, force: bool) -> Result<()>;
    /// Register modules in the aggregator so they are actually built.
    fn add_imports(&mut self, modules: &[ModuleName]) -> Result<Vec<ModuleName>>;
}

/// The resolved configuration, as the use cases need it: no paths to resolve,
/// no TOML, just the sources and the two directories that matter.
#[derive(Debug, Clone)]
pub struct Workspace {
    pub sources: Sources,
    /// Where `dt add` materializes declarations.
    pub vendor_dir: PathBuf,
    /// The module that directory corresponds to, e.g. `Transformer.Vendor`.
    pub vendor_module: ModuleName,
    /// The project's own namespace, so `dt dup` can tell local from upstream.
    pub namespace: String,
}

impl Workspace {
    pub fn meta(&self, id: &SourceId) -> Option<SourceMeta> {
        self.sources.get(id).cloned()
    }
}
