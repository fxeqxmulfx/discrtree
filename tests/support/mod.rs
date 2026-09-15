//! Shared fixtures: a temporary directory, and in-memory doubles for every
//! port. Keeping the doubles here rather than in `src/` means the use cases
//! are exercised across the real crate boundary.

#![allow(dead_code)]

use discrtree::application::ports::{DeclRepo, ProjectWriter, SourceFiles};
use discrtree::domain::decl::{ArgHead, Decl, DeclKind, Shape, Span};
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::query::Query;
use discrtree::domain::source::{SourceId, SourceKind, SourceMeta, Sources};
use discrtree::error::Result;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A directory that removes itself. Enough for these tests, and one fewer
/// dependency than a crate for it.
pub struct TempDir(PathBuf);

impl TempDir {
    pub fn new(tag: &str) -> TempDir {
        let base = std::env::temp_dir().join(format!(
            "discrtree-test-{tag}-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        std::fs::create_dir_all(&base).expect("create temp dir");
        TempDir(base)
    }

    pub fn path(&self) -> &Path {
        &self.0
    }

    pub fn write(&self, rel: &str, contents: &str) -> PathBuf {
        let path = self.0.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).expect("create parent");
        }
        std::fs::write(&path, contents).expect("write fixture");
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// A declaration built the way the tests want to talk about one.
pub fn decl(name: &str, source: &str, module: &str) -> Decl {
    Decl::stub(name, source, module)
}

pub fn theorem(name: &str, source: &str, module: &str, concl: &str, deps: &[&str]) -> Decl {
    let mut d = Decl::stub(name, source, module);
    d.kind = DeclKind::Theorem;
    d.shape = Shape::new(Some(DeclName::new(concl)), vec![ArgHead::Any, ArgHead::Any]);
    d.deps = deps.iter().map(|n| DeclName::new(*n)).collect();
    d.consts = d.deps.clone();
    d.span = Some(Span::new(1, 2));
    d
}

/// Every source these tests use: one compiled and importable, one compiled but
/// not importable (the project's own code, which has to be copied), and one
/// text corpus.
pub fn sources() -> Sources {
    Sources::new(vec![
        SourceMeta {
            id: SourceId::new("mathlib"),
            kind: SourceKind::Lake,
            elaborated: true,
            importable: true,
            rev: Some("v4.33.1".into()),
            license: Some("Apache-2.0".into()),
            attribution: Some("The mathlib Community".into()),
        },
        SourceMeta {
            id: SourceId::new("other"),
            kind: SourceKind::Lake,
            elaborated: true,
            importable: false,
            rev: None,
            license: Some("Apache-2.0".into()),
            attribution: None,
        },
        SourceMeta {
            id: SourceId::new("flt"),
            kind: SourceKind::Git,
            elaborated: false,
            importable: false,
            rev: Some("deadbeef".into()),
            license: Some("Apache-2.0".into()),
            attribution: None,
        },
    ])
}

/// A repository over a fixed list of rows, applying the domain's own matching
/// rule. That it and SQLite must agree is the point of having the rule in one
/// place.
pub struct FakeRepo {
    pub decls: Vec<Decl>,
}

impl DeclRepo for FakeRepo {
    fn get(&self, name: &DeclName) -> Result<Option<Decl>> {
        Ok(self.decls.iter().find(|d| &d.name == name).cloned())
    }

    fn find(&self, query: &Query) -> Result<Vec<Decl>> {
        Ok(self.decls.iter().filter(|d| query.matches(d)).cloned().collect())
    }

    fn get_many(&self, names: &[DeclName]) -> Result<Vec<Decl>> {
        Ok(names.iter().filter_map(|n| self.decls.iter().find(|d| &d.name == n).cloned()).collect())
    }

    /// The same rule SQLite applies: the smallest strictly-containing span in
    /// the same module. Written out again here because the two agreeing is what
    /// makes the fake worth testing against.
    fn enclosing(&self, of: &Decl) -> Result<Option<Decl>> {
        let Some(span) = of.span else { return Ok(None) };
        Ok(self
            .decls
            .iter()
            .filter(|d| d.module == of.module && d.source == of.source && d.name != of.name)
            .filter(|d| {
                d.span.is_some_and(|s| {
                    s.start <= span.start
                        && s.end >= span.end
                        && (s.start, s.end) != (span.start, span.end)
                })
            })
            .min_by_key(|d| d.span.map(|s| s.end - s.start).unwrap_or(u32::MAX))
            .cloned())
    }

    fn counts(&self) -> Result<Vec<(SourceId, usize)>> {
        let mut by: BTreeMap<SourceId, usize> = BTreeMap::new();
        for d in &self.decls {
            *by.entry(d.source.clone()).or_default() += 1;
        }
        Ok(by.into_iter().collect())
    }
}

/// Module text keyed by (source, module), so `dt show` and `dt add` can read
/// declarations without a filesystem.
pub struct FakeFiles {
    pub modules: BTreeMap<(String, String), String>,
}

impl FakeFiles {
    pub fn new() -> FakeFiles {
        FakeFiles { modules: BTreeMap::new() }
    }

    pub fn with(mut self, source: &str, module: &str, text: &str) -> FakeFiles {
        self.modules.insert((source.into(), module.into()), text.into());
        self
    }
}

impl SourceFiles for FakeFiles {
    fn read_module(&self, source: &SourceId, module: &ModuleName) -> Result<String> {
        match self.modules.get(&(source.to_string(), module.as_str().to_string())) {
            Some(t) => Ok(t.clone()),
            None => Err(discrtree::error::Error::new(format!("{source}: no module {module}"))),
        }
    }

    fn list_modules(&self, source: &SourceId) -> Result<Vec<(ModuleName, PathBuf)>> {
        Ok(self
            .modules
            .keys()
            .filter(|(s, _)| s == source.as_str())
            .map(|(_, m)| (ModuleName::new(m.clone()), PathBuf::from(m)))
            .collect())
    }

    fn location(&self, source: &SourceId) -> PathBuf {
        PathBuf::from(source.as_str())
    }
}

/// Records what would have been written. Nothing reaches the disk.
#[derive(Default)]
pub struct FakeWriter {
    pub files: Vec<(PathBuf, String)>,
    pub imports: Vec<ModuleName>,
}

impl ProjectWriter for FakeWriter {
    fn write_module(&mut self, path: &Path, contents: &str, _force: bool) -> Result<()> {
        self.files.push((path.to_path_buf(), contents.to_string()));
        Ok(())
    }

    fn add_imports(&mut self, modules: &[ModuleName]) -> Result<Vec<ModuleName>> {
        self.imports.extend_from_slice(modules);
        Ok(modules.to_vec())
    }
}

/// Revisions a test decides on, so staleness can be exercised without a
/// checkout: a source is at whatever the map says, and at nothing otherwise.
#[derive(Default)]
pub struct FakeRevisions(pub std::collections::BTreeMap<String, String>);

impl FakeRevisions {
    pub fn at(pairs: &[(&str, &str)]) -> FakeRevisions {
        FakeRevisions(pairs.iter().map(|(a, b)| (a.to_string(), b.to_string())).collect())
    }
}

impl discrtree::application::ports::Revisions for FakeRevisions {
    fn current(&self, source: &SourceId) -> discrtree::error::Result<Option<String>> {
        Ok(self.0.get(source.as_str()).cloned())
    }
}

/// A build carrying packages no source covers. `("batteries", "Batteries")` is
/// a package directory and the library root it provides.
pub struct FakePackages(pub Vec<discrtree::application::ports::Package>);

impl FakePackages {
    pub fn with(pairs: &[(&str, &str)]) -> FakePackages {
        FakePackages(
            pairs
                .iter()
                .map(|(name, root)| discrtree::application::ports::Package {
                    name: name.to_string(),
                    roots: vec![root.to_string()],
                })
                .collect(),
        )
    }
}

impl discrtree::application::ports::Packages for FakePackages {
    fn unindexed(&self) -> Vec<discrtree::application::ports::Package> {
        self.0.clone()
    }
}
