//! The boundary. Every use case is written against these traits, and every one
//! of them has a test double in `tests/`.

use crate::domain::decl::Decl;
use crate::domain::lean_core;
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

    /// The smallest declaration whose source range strictly contains `span` in
    /// the same module, if any.
    ///
    /// This is how a generated declaration is recognised without asking Lean.
    /// `to_additive` gives `Finset.sum_image` the range of the attribute block
    /// sitting inside `Finset.prod_image`, so the declaration that produced it
    /// is the one wrapped around it. A store that cannot answer says so, and
    /// `dt show` then reports only that the lines declare nothing.
    fn enclosing(&self, _of: &Decl) -> Result<Option<Decl>> {
        Ok(None)
    }

    /// What the source was when it was indexed, if the store remembers.
    fn provenance(&self, _source: &SourceId) -> Result<Option<Provenance>> {
        Ok(None)
    }
}

/// Writing the index.
pub trait DeclSink {
    fn put(&mut self, decls: &[Decl]) -> Result<()>;
    /// Called once when every row is in: the moment to build the text index.
    fn finish(&mut self) -> Result<()>;

    /// Record what the source was when it was indexed. A sink that cannot
    /// remember — the JSONL writer — simply does not, and the caller then has
    /// to do the work every time, which is correct if wasteful.
    fn record(&mut self, _source: &SourceId, _was: &Provenance) -> Result<()> {
        Ok(())
    }
}

/// What a source was at the moment it went into the index.
///
/// Two different questions are answered from this, and conflating them is how
/// an index goes quietly stale. `stamp` fingerprints the *input* — the JSONL a
/// compiled source was dumped to, the checkout a text source was read from —
/// and deciding whether `dt index` has anything to do is exactly comparing it.
/// `revision` names the *upstream* the input itself came from, which is what
/// tells you the dump is older than the Mathlib you are now building against.
/// An index can be perfectly current with respect to its input and months
/// behind the library.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    pub revision: Option<String>,
    /// `None` when the input cannot be fingerprinted cheaply — a text source
    /// that is a plain directory rather than a checkout. The work is then done
    /// every time, which is wasteful and correct; guessing would be neither.
    pub stamp: Option<String>,
    /// Seconds since the Unix epoch. Stored as an instant and reported as an
    /// age, because "three days old" answers the question and a timestamp
    /// makes the reader do the subtraction.
    pub indexed_at: u64,
    pub decls: usize,
}

/// The revision a source is at on disk right now, as opposed to the one the
/// index remembers. Git answers by `rev-parse`; a lake dependency answers from
/// the manifest the build resolved.
pub trait Revisions {
    fn current(&self, source: &SourceId) -> Result<Option<String>>;
}

/// A package a `lake` build resolved: the directory it sits in, and the module
/// prefixes it provides.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Package {
    /// The directory name under `.lake/packages`, which is what a source entry
    /// would have to name to index it.
    pub name: String,
    /// The library roots, e.g. `Batteries`. Anything under one of these already
    /// resolves from an `import` line in the project; only the index is missing
    /// it, which is what makes the gap invisible.
    pub roots: Vec<String>,
}

/// The Lean toolchain the project builds against, and whether its own library
/// is in the index.
///
/// Core is a corpus like the packages are, and the one that cannot be walked:
/// `Init` and `Std` ship inside the toolchain, and the modules that would say
/// what they declare are exactly the ones nobody dumped. So what it provides is
/// written down in [`lean_core`](crate::domain::lean_core) and all that is read
/// from disk is which toolchain, and whether a source covers it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Toolchain {
    /// As `lean-toolchain` spells it, e.g. `leanprover/lean4:v4.33.1`.
    pub name: String,
    /// Whether a configured source imports one of core's roots.
    pub indexed: bool,
}

/// A corpus the build can import that the index does not cover.
///
/// Two of them, and they are named apart because the repair is not the same
/// sentence: a package is a directory that is already on the machine, and core
/// is inside the toolchain. Telling a reader to `dt dump batteries` when what
/// is missing is `Int.add_one_le_iff` would send them to the wrong place.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Missing {
    /// A lake package, by its directory name under `.lake/packages`.
    Package(String),
    /// The toolchain's own library, by the toolchain's name.
    Core(String),
}

/// What the build can import, as against what the index holds.
///
/// A `discrtree.toml` names Mathlib and stops there, and everything Mathlib is
/// built on — batteries, aesop, Qq, and under all of them core itself — is then
/// importable from the project and absent from every search. No question asked
/// of the index can discover that: a corpus that was never dumped leaves
/// nothing behind to find. What the build resolved is the only evidence there
/// is.
pub trait Build {
    /// Every resolved package that no configured source points at.
    fn unindexed(&self) -> Vec<Package>;

    /// The toolchain the project pins, when it pins one.
    fn toolchain(&self) -> Option<Toolchain> {
        None
    }

    /// The unindexed corpus that provides this module prefix, if one does.
    fn module(&self, prefix: &str) -> Option<Missing> {
        if let Some(p) = self.package(prefix) {
            return Some(Missing::Package(p.name));
        }
        self.absent_core().filter(|_| lean_core::has_module(prefix)).map(Missing::Core)
    }

    /// The unindexed corpus that declares in this name's namespace, if one
    /// does. `Batteries.RBNode.Balanced` comes back as the package `batteries`
    /// and `Int.add_one_le_iff` as core, because the answer to both is a source
    /// that was never added.
    fn declaring(&self, name: &str) -> Option<Missing> {
        if let Some(p) = self.package(name) {
            return Some(Missing::Package(p.name));
        }
        self.absent_core().filter(|_| lean_core::declares(name)).map(Missing::Core)
    }

    /// The unindexed package whose library root this sits under. A package's
    /// module prefix and its namespace are the same string, so one lookup
    /// answers for both.
    fn package(&self, prefix: &str) -> Option<Package> {
        self.unindexed().into_iter().find(|p| p.roots.iter().any(|r| under(r, prefix)))
    }

    /// The toolchain, and only when its library is not in the index.
    fn absent_core(&self) -> Option<String> {
        self.toolchain().filter(|t| !t.indexed).map(|t| t.name)
    }
}

/// Whether `prefix` is the root module or something below it. `Batteries` and
/// `Batteries.Data` are, `BatteriesTest` is not.
fn under(root: &str, prefix: &str) -> bool {
    prefix == root || prefix.strip_prefix(root).is_some_and(|rest| rest.starts_with('.'))
}

/// A build with nothing beside its sources: a project that is not a lake
/// project at all, and every test that is not about what is missing.
pub struct NoBuild;

impl Build for NoBuild {
    fn unindexed(&self) -> Vec<Package> {
        Vec::new()
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    struct Resolved {
        packages: Vec<Package>,
        toolchain: Option<Toolchain>,
    }

    impl Build for Resolved {
        fn unindexed(&self) -> Vec<Package> {
            self.packages.clone()
        }
        fn toolchain(&self) -> Option<Toolchain> {
            self.toolchain.clone()
        }
    }

    fn build(core_indexed: bool) -> Resolved {
        Resolved {
            packages: vec![
                Package { name: "batteries".into(), roots: vec!["Batteries".into()] },
                Package { name: "importGraph".into(), roots: vec!["ImportGraph".into()] },
            ],
            toolchain: Some(Toolchain {
                name: "leanprover/lean4:v4.33.1".into(),
                indexed: core_indexed,
            }),
        }
    }

    #[test]
    fn a_prefix_is_traced_to_the_package_that_provides_it() {
        let b = build(true);
        assert_eq!(b.module("Batteries"), Some(Missing::Package("batteries".into())));
        assert_eq!(b.declaring("Batteries.Data.RBMap"), Some(Missing::Package("batteries".into())));
        assert_eq!(b.module("ImportGraph.Cli"), Some(Missing::Package("importGraph".into())));
    }

    #[test]
    fn a_root_is_a_module_boundary_not_a_string_prefix() {
        // `BatteriesTest` starts with `Batteries` and is a different library.
        // Claiming the package provides it would send the reader to add a
        // source that does not have what they asked for.
        let b = build(true);
        assert!(b.declaring("BatteriesTest").is_none());
        assert!(b.module("Mathlib.Analysis").is_none());
    }

    #[test]
    fn core_answers_for_its_namespaces_by_name_and_its_roots_by_module() {
        let b = build(false);
        let core = Missing::Core("leanprover/lean4:v4.33.1".into());
        assert_eq!(b.declaring("Int.add_one_le_iff"), Some(core.clone()));
        assert_eq!(b.module("Init.Data.Int.Order"), Some(core));
        // And not the other way round: `Int` is no module and `Init` is no
        // namespace, so neither question may be answered with the other's list.
        assert!(b.module("Int").is_none());
        assert!(b.declaring("Mathlib.Analysis.exp").is_none());
    }

    #[test]
    fn an_indexed_core_is_not_reported_missing() {
        let b = build(true);
        assert!(b.declaring("Int.add_one_le_iff").is_none());
        assert!(b.module("Init.Data.Int.Order").is_none());
    }

    #[test]
    fn a_build_with_nothing_beside_its_sources_traces_nothing() {
        assert!(NoBuild.declaring("Batteries").is_none());
        assert!(NoBuild.declaring("Int.add_one_le_iff").is_none(), "no toolchain, no claim");
        assert!(NoBuild.unindexed().is_empty());
    }
}
