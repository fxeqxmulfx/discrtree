//! Phase 0. One `discrtree.toml` at the project root declares where the tool
//! writes and what it indexes; everything else is derived.

use crate::application::ports::Workspace;
use crate::domain::name::ModuleName;
use crate::domain::source::{SourceId, SourceKind, SourceMeta, Sources};
use crate::error::{Error, Result, bail};
use serde::Deserialize;
use std::path::{Path, PathBuf};

pub const FILE_NAME: &str = "discrtree.toml";

#[derive(Debug, Deserialize)]
pub struct Config {
    pub project: Project,
    #[serde(default)]
    pub index: Index,
    #[serde(rename = "source", default)]
    pub sources: Vec<Source>,
    /// Directory holding the config file. Relative paths resolve against
    /// `project.root`, which resolves against this.
    #[serde(skip)]
    pub base: PathBuf,
}

#[derive(Debug, Deserialize)]
pub struct Project {
    #[serde(default = "dot")]
    pub root: PathBuf,
    #[serde(default = "src_dir")]
    pub src: PathBuf,
    pub namespace: String,
    /// The aggregator: what is already reachable from a build. A module that is
    /// not reachable from it is not built.
    pub imports: PathBuf,
    /// Where `dt add` materializes declarations.
    pub vendor: PathBuf,
}

#[derive(Debug, Deserialize)]
pub struct Index {
    #[serde(default = "default_db")]
    pub db: PathBuf,
    #[serde(default = "default_raw")]
    pub raw: PathBuf,
}

impl Default for Index {
    fn default() -> Self {
        Index { db: default_db(), raw: default_raw() }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    Lake,
    Local,
    Git,
}

impl From<Kind> for SourceKind {
    fn from(k: Kind) -> SourceKind {
        match k {
            Kind::Lake => SourceKind::Lake,
            Kind::Local => SourceKind::Local,
            Kind::Git => SourceKind::Git,
        }
    }
}

#[derive(Debug, Deserialize)]
pub struct Source {
    pub name: String,
    pub kind: Kind,
    /// Where the `.lean` files live, relative to the project root.
    #[serde(default)]
    pub path: Option<PathBuf>,
    /// Root Lean module, e.g. `Mathlib`: what the dump imports and what filters
    /// the environment walk. Required for a compiled source.
    #[serde(default)]
    pub root: Option<String>,
    /// Extra module prefixes to keep beyond `root`.
    #[serde(default)]
    pub modules: Vec<String>,
    #[serde(default)]
    pub url: Option<String>,
    #[serde(default)]
    pub rev: Option<String>,
    /// Sparse-checkout directories. Empty means a full checkout.
    #[serde(default)]
    pub sparse: Vec<String>,
    /// Path fragments never scanned, however large the directory.
    #[serde(default)]
    pub exclude: Vec<String>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default)]
    pub attribution: Option<String>,
    /// Overrides for the two properties derived from `kind`. A `git` source
    /// that someone does build can set both to true.
    #[serde(default)]
    pub elaborated: Option<bool>,
    #[serde(default)]
    pub importable: Option<bool>,
}

fn dot() -> PathBuf {
    PathBuf::from(".")
}
fn src_dir() -> PathBuf {
    PathBuf::from("src")
}
fn default_db() -> PathBuf {
    PathBuf::from(".discrtree/index.db")
}
fn default_raw() -> PathBuf {
    PathBuf::from(".discrtree/jsonl")
}

impl Source {
    pub fn elaborated(&self) -> bool {
        self.elaborated.unwrap_or(SourceKind::from(self.kind).default_elaborated())
    }

    pub fn importable(&self) -> bool {
        self.importable.unwrap_or(SourceKind::from(self.kind).default_importable())
    }

    pub fn module_prefixes(&self) -> Vec<String> {
        let mut v = self.modules.clone();
        if let Some(r) = &self.root {
            v.push(r.clone());
        }
        v
    }

    pub fn meta(&self) -> SourceMeta {
        SourceMeta {
            id: SourceId::new(self.name.clone()),
            kind: self.kind.into(),
            elaborated: self.elaborated(),
            importable: self.importable(),
            rev: self.rev.clone(),
            license: self.license.clone(),
            attribution: self.attribution.clone(),
        }
    }
}

impl Config {
    /// Read the config, searching upwards from the working directory when no
    /// path is given.
    pub fn load(explicit: Option<&Path>) -> Result<Config> {
        let file = match explicit {
            Some(p) => p.to_path_buf(),
            None => find_upwards(FILE_NAME)?,
        };
        let text = std::fs::read_to_string(&file)
            .map_err(|e| Error::new(format!("{}: {e}", file.display())))?;
        Config::parse(&text, file.parent().unwrap_or(Path::new(".")))
    }

    pub fn parse(text: &str, base: &Path) -> Result<Config> {
        let mut cfg: Config = toml::from_str(text)?;
        cfg.base = base.to_path_buf();
        cfg.validate()?;
        Ok(cfg)
    }

    fn validate(&self) -> Result<()> {
        let mut seen = std::collections::HashSet::new();
        for s in &self.sources {
            if !seen.insert(&s.name) {
                bail!("{FILE_NAME}: two sources named `{}`", s.name);
            }
            if s.elaborated() && s.root.is_none() {
                bail!(
                    "{FILE_NAME}: source `{}` is compiled, so it needs `root = \"<Module>\"` \
                     — the module the dump imports",
                    s.name
                );
            }
            if s.kind == Kind::Git && s.url.is_none() && s.path.is_none() {
                bail!("{FILE_NAME}: source `{}` needs a `url` or a `path`", s.name);
            }
        }
        Ok(())
    }

    pub fn root(&self) -> PathBuf {
        absolute(&self.base, &self.project.root)
    }

    pub fn resolve(&self, p: &Path) -> PathBuf {
        absolute(&self.root(), p)
    }

    pub fn db_path(&self) -> PathBuf {
        self.resolve(&self.index.db)
    }

    pub fn raw_dir(&self) -> PathBuf {
        self.resolve(&self.index.raw)
    }

    pub fn vendor_dir(&self) -> PathBuf {
        self.resolve(&self.project.vendor)
    }

    pub fn imports_file(&self) -> PathBuf {
        self.resolve(&self.project.imports)
    }

    /// Where a `git` source is checked out when it declares no `path`.
    pub fn source_dir(&self, s: &Source) -> PathBuf {
        match &s.path {
            Some(p) => self.resolve(p),
            None => self.raw_dir().parent().unwrap_or(Path::new(".")).join("sources").join(&s.name),
        }
    }

    pub fn jsonl_path(&self, s: &Source) -> PathBuf {
        self.raw_dir().join(format!("{}.jsonl", s.name))
    }

    pub fn source(&self, name: &str) -> Result<&Source> {
        match self.sources.iter().find(|s| s.name == name) {
            Some(s) => Ok(s),
            None => {
                let known: Vec<&str> = self.sources.iter().map(|s| s.name.as_str()).collect();
                bail!("no source named `{name}`; known: {}", known.join(", "))
            }
        }
    }

    /// The module the vendor directory corresponds to. Derived from the project
    /// namespace and the vendor path, so a full name stays guessable from a
    /// path: `src/Transformer/Vendor` under namespace `Transformer` is
    /// `Transformer.Vendor`.
    pub fn vendor_module(&self) -> ModuleName {
        let vendor = self.resolve(&self.project.vendor);
        let src = self.resolve(&self.project.src);
        match vendor.strip_prefix(&src) {
            Ok(rel) => {
                let parts: Vec<String> = rel
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy().into_owned())
                    .collect();
                ModuleName::new(parts.join("."))
            }
            // A vendor directory outside `src` cannot be named from the path,
            // so fall back to the namespace and say where it went.
            Err(_) => ModuleName::new(format!("{}.Vendor", self.project.namespace)),
        }
    }

    /// The configuration as the use cases need it.
    pub fn workspace(&self) -> Workspace {
        Workspace {
            sources: Sources::new(self.sources.iter().map(Source::meta).collect()),
            vendor_dir: self.vendor_dir(),
            vendor_module: self.vendor_module(),
            namespace: self.project.namespace.clone(),
        }
    }
}

fn absolute(base: &Path, p: &Path) -> PathBuf {
    if p.is_absolute() { p.to_path_buf() } else { base.join(p) }
}

fn find_upwards(name: &str) -> Result<PathBuf> {
    let mut dir = std::env::current_dir()?;
    loop {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Ok(candidate);
        }
        if !dir.pop() {
            bail!("no {name} here or in any parent directory; run `dt init` in the project root")
        }
    }
}

/// The file `dt init` writes.
pub const TEMPLATE: &str = r#"# discrtree — what to index and where to write.
# Two properties drive everything and are derived from `kind`:
#
#   kind            elaborated   importable
#   lake, local     true         true
#   git             false        false
#
# `elaborated` decides whether shape search and exact dependencies are
# available. `importable` decides whether a dependency collapses into an
# `import` line or has to be copied. Either can be overridden per source.

[project]
root      = "."
src       = "src"
namespace = "Transformer"
imports   = "src/Transformer.lean"      # what is already reachable
vendor    = "src/Transformer/Vendor"    # where materialized declarations land

[index]
db  = ".discrtree/index.db"
raw = ".discrtree/jsonl"

[[source]]
name = "project"
kind = "local"
path = "src"
root = "Transformer"

[[source]]
name = "mathlib"
kind = "lake"
path = ".lake/packages/mathlib"
root = "Mathlib"
rev  = "v4.33.1"
"#;

#[cfg(test)]
mod tests {
    use super::*;

    const SAMPLE: &str = r#"
[project]
root = "."
src = "src"
namespace = "Transformer"
imports = "src/Transformer.lean"
vendor = "src/Transformer/Vendor"

[[source]]
name = "project"
kind = "local"
path = "src"
root = "Transformer"

[[source]]
name = "mathlib"
kind = "lake"
path = ".lake/packages/mathlib"
root = "Mathlib"
rev = "v4.33.1"

[[source]]
name = "flt"
kind = "git"
url = "https://example.invalid/flt"
rev = "main"
sparse = ["Theorems", "Definitions"]
exclude = ["html"]
license = "Apache-2.0"
"#;

    fn cfg() -> Config {
        Config::parse(SAMPLE, Path::new("/p")).unwrap()
    }

    #[test]
    fn the_two_properties_are_derived_from_kind() {
        let c = cfg();
        let mathlib = c.source("mathlib").unwrap();
        assert!(mathlib.elaborated() && mathlib.importable());
        let flt = c.source("flt").unwrap();
        assert!(!flt.elaborated() && !flt.importable());
    }

    #[test]
    fn an_override_wins_over_the_kind() {
        // A `git` source that someone does build declares both flags and the
        // root module the dump would import.
        let text = SAMPLE.to_string() + "root = \"FLT\"\nelaborated = true\nimportable = true\n";
        let c = Config::parse(&text, Path::new("/p")).unwrap();
        let flt = c.source("flt").unwrap();
        assert!(flt.elaborated() && flt.importable());
    }

    #[test]
    fn overriding_elaborated_without_a_root_module_is_rejected() {
        let text = SAMPLE.to_string() + "elaborated = true\n";
        let err = Config::parse(&text, Path::new("/p")).unwrap_err().to_string();
        assert!(err.contains("needs `root"), "got: {err}");
    }

    #[test]
    fn paths_resolve_against_the_project_root() {
        let c = cfg();
        assert_eq!(c.db_path(), Path::new("/p/./.discrtree/index.db"));
        assert_eq!(
            c.jsonl_path(c.source("mathlib").unwrap()),
            Path::new("/p/./.discrtree/jsonl/mathlib.jsonl")
        );
    }

    #[test]
    fn a_git_source_without_a_path_gets_one_under_the_index_directory() {
        let c = cfg();
        let flt = c.source("flt").unwrap();
        assert!(c.source_dir(flt).ends_with("sources/flt"));
    }

    #[test]
    fn the_vendor_module_is_derived_from_the_vendor_path() {
        assert_eq!(cfg().vendor_module().as_str(), "Transformer.Vendor");
    }

    #[test]
    fn a_compiled_source_without_a_root_module_is_rejected() {
        let text = SAMPLE.replace("root = \"Mathlib\"\n", "");
        let err = Config::parse(&text, Path::new("/p")).unwrap_err().to_string();
        assert!(err.contains("needs `root"), "got: {err}");
    }

    #[test]
    fn duplicate_source_names_are_rejected() {
        let text =
            SAMPLE.to_string() + "\n[[source]]\nname = \"flt\"\nkind = \"git\"\nurl = \"x\"\n";
        let err = Config::parse(&text, Path::new("/p")).unwrap_err().to_string();
        assert!(err.contains("two sources named"), "got: {err}");
    }

    #[test]
    fn the_template_parses() {
        let c = Config::parse(TEMPLATE, Path::new("/p")).unwrap();
        assert_eq!(c.sources.len(), 2);
        assert_eq!(c.workspace().namespace, "Transformer");
    }

    #[test]
    fn module_prefixes_include_the_root() {
        let c = cfg();
        assert_eq!(c.source("mathlib").unwrap().module_prefixes(), vec!["Mathlib"]);
    }
}
