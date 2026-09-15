//! Phase 1 through a process boundary.
//!
//! Only the elaborator can read `.olean` and hand back an elaborated type with
//! notation expanded — without it a sum never becomes `Finset.sum` and shape
//! search has no ground to stand on. So the dump is Lean, and this is the whole
//! of the Rust side's knowledge of it: splice the right imports into
//! `lean/dump.lean`, set four environment variables, run `lake env lean`.

use crate::application::ports::{Build, DumpSpec, Elaborator, Package, Toolchain};
use crate::domain::lean_core;
use crate::error::{Error, Result, bail};
use crate::infrastructure::config::{Config, Source};
use std::path::{Path, PathBuf};
use std::process::Command;

/// The dump script, compiled in. Shipping it inside the binary removes the one
/// failure mode a two-language tool otherwise has: half of it not installed.
pub const DUMP_LEAN: &str = include_str!("../../lean/dump.lean");

const BEGIN: &str = "-- BEGIN IMPORTS";
const END: &str = "-- END IMPORTS";

/// Put the source's root module into the script's import block.
pub fn splice_imports(script: &str, root: &str) -> Result<String> {
    let (Some(start), Some(end)) = (script.find(BEGIN), script.find(END)) else {
        bail!("lean/dump.lean has lost its `{BEGIN}` / `{END}` markers")
    };
    let mut out = String::with_capacity(script.len() + 64);
    out.push_str(&script[..start]);
    out.push_str(BEGIN);
    out.push_str(" (rewritten by `dt dump`)\nimport ");
    out.push_str(root);
    out.push('\n');
    out.push_str(&script[end..]);
    Ok(out)
}

pub struct LakeElaborator {
    /// Where `lake` runs: the directory holding `lakefile.toml`.
    pub project_root: PathBuf,
    /// Where the spliced script is written.
    pub work_dir: PathBuf,
    /// Printed to stderr as the dump runs.
    pub verbose: bool,
}

impl Elaborator for LakeElaborator {
    fn dump(&self, spec: &DumpSpec) -> Result<PathBuf> {
        std::fs::create_dir_all(&self.work_dir)?;
        if let Some(parent) = spec.out.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let script = self.work_dir.join(format!("dump_{}.lean", spec.source));
        std::fs::write(&script, splice_imports(DUMP_LEAN, &spec.root)?)?;

        if self.verbose {
            eprintln!(
                "dt: dumping `{}` (import {}) via lake env lean; this reads the whole environment \
                 and takes minutes",
                spec.source, spec.root
            );
        }
        let status = Command::new("lake")
            .arg("env")
            .arg("lean")
            .arg(&script)
            .current_dir(&self.project_root)
            .env("DISCRTREE_OUT", &spec.out)
            .env("DISCRTREE_SOURCE", spec.source.as_str())
            .env("DISCRTREE_MODULES", spec.modules.join(","))
            .env("DISCRTREE_DEPS", if spec.with_deps { "1" } else { "0" })
            .status()
            .map_err(|e| {
                Error::new(format!(
                    "could not run `lake` in {}: {e}; is elan on PATH?",
                    self.project_root.display()
                ))
            })?;
        if !status.success() {
            bail!(
                "lake env lean failed for source `{}` (exit {}); the script is at {}",
                spec.source,
                status.code().unwrap_or(-1),
                script.display()
            )
        }
        if !spec.out.exists() {
            bail!("the dump reported success but wrote nothing to {}", spec.out.display())
        }
        Ok(spec.out.clone())
    }
}

/// Where `lake` puts the dependencies it resolved, relative to the project root.
pub const PACKAGES: &str = ".lake/packages";

/// The dependencies a build resolved, minus the ones a source already indexes.
///
/// Read off the directory rather than out of `lake-manifest.json` on purpose:
/// the manifest says what was resolved, the directory holds what was actually
/// fetched and built, and an `import` line resolves against the second of
/// those. A package listed but never fetched is not a corpus anyone is missing.
pub struct LakeBuild {
    dir: PathBuf,
    /// The package directories the configured sources point at, canonical, so
    /// that `.lake/packages/mathlib` and `./.lake/packages/mathlib` are one
    /// directory rather than two.
    indexed: Vec<PathBuf>,
    toolchain: Option<Toolchain>,
}

impl LakeBuild {
    pub fn read(cfg: &Config) -> LakeBuild {
        let indexed = cfg
            .sources
            .iter()
            .filter_map(|s| s.path.as_ref())
            .map(|p| real(&cfg.resolve(p)))
            .collect();
        LakeBuild { dir: cfg.root().join(PACKAGES), indexed, toolchain: toolchain(cfg) }
    }
}

/// The file a lake project pins its toolchain in, one line, at the project
/// root.
pub const TOOLCHAIN: &str = "lean-toolchain";

/// Which toolchain the project builds against, and whether its library is
/// indexed.
///
/// A source covers core when it imports one of core's roots — that is what a
/// dump of core would have to say, and it is a surer signal than the path,
/// which may point into elan, into a source tarball, or at a checkout of
/// lean4. A project with no `lean-toolchain` is not one this can speak about,
/// and says nothing rather than guessing.
fn toolchain(cfg: &Config) -> Option<Toolchain> {
    let name = std::fs::read_to_string(cfg.root().join(TOOLCHAIN)).ok()?;
    let name = name.trim();
    if name.is_empty() {
        return None;
    }
    // By the module it dumps rather than by its kind: a `lake` source pointed
    // at `Init` indexes core just as truly as a `core` one does, and what this
    // flag decides is whether a `no match` under `Nat.` gets blamed on core.
    let indexed = cfg
        .sources
        .iter()
        .filter_map(Source::root_module)
        .any(|r| lean_core::ROOTS.contains(&r.as_str()));
    Some(Toolchain { name: name.to_owned(), indexed })
}

/// Where a toolchain keeps the `.lean` sources of its own library, relative to
/// its prefix. `Init/Data/List/Basic.lean` sits directly under this, so the
/// module-to-path rule every other source follows works here unchanged.
const CORE_SRC: &str = "src/lean";

/// The directory holding core's source text, or nothing.
///
/// Two ways of asking, cheapest first. Elan lays its toolchains out under
/// `$ELAN_HOME/toolchains/<name with its separators folded into dashes>`, which
/// costs one directory test and no process at all. When that misses -- a
/// toolchain installed some other way, or a name elan spells differently --
/// `lean` is asked where it lives.
///
/// Asked from the project root, always: `lean --print-prefix` run anywhere else
/// resolves elan's *default* toolchain, and if that one is not installed the
/// question becomes a three-gigabyte download nobody asked for.
pub fn core_src(project_root: &Path, toolchain: Option<&str>) -> Option<PathBuf> {
    if let Some(name) = toolchain {
        let dir = elan_home()?.join("toolchains").join(elan_dir_name(name)).join(CORE_SRC);
        if dir.is_dir() {
            return Some(dir);
        }
    }
    let out = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(project_root)
        .output()
        .ok()
        .filter(|o| o.status.success())?;
    let prefix = String::from_utf8_lossy(&out.stdout).trim().to_owned();
    let dir = PathBuf::from(prefix).join(CORE_SRC);
    dir.is_dir().then_some(dir)
}

/// `leanprover/lean4:v4.33.1` as elan spells it on disk.
fn elan_dir_name(toolchain: &str) -> String {
    toolchain.replace('/', "--").replace(':', "---")
}

fn elan_home() -> Option<PathBuf> {
    if let Ok(home) = std::env::var("ELAN_HOME") {
        return Some(PathBuf::from(home));
    }
    std::env::var("HOME").ok().map(|h| PathBuf::from(h).join(".elan"))
}

impl Build for LakeBuild {
    fn unindexed(&self) -> Vec<Package> {
        let Ok(entries) = std::fs::read_dir(&self.dir) else { return Vec::new() };
        let mut out: Vec<Package> = entries
            .flatten()
            .filter(|e| e.file_type().is_ok_and(|t| t.is_dir()))
            .filter(|e| !e.file_name().to_string_lossy().starts_with('.'))
            .filter(|e| !self.indexed.contains(&real(&e.path())))
            .map(|e| Package {
                name: e.file_name().to_string_lossy().into_owned(),
                roots: roots(&e.path()),
            })
            .collect();
        // A directory listing comes back in whatever order the filesystem keeps
        // it, and a list that reshuffles itself between runs reads as change.
        // Folded, because `Cli` and `aesop` are peers and sorting by byte value
        // would put every capitalized package in its own block.
        out.sort_by_key(|p| p.name.to_lowercase());
        out
    }

    fn toolchain(&self) -> Option<Toolchain> {
        self.toolchain.clone()
    }
}

/// The library roots a package provides: an `X.lean` sitting beside a directory
/// `X`.
///
/// That pairing is the convention every `import` line relies on, and it is the
/// only part of a package readable without running Lake — half of these declare
/// their libraries in `lakefile.lean`, which is a program, not data. A package
/// whose layout does not follow it still gets listed by `dt status`; it just
/// cannot be traced back to from a module prefix.
fn roots(dir: &Path) -> Vec<String> {
    let Ok(entries) = std::fs::read_dir(dir) else { return Vec::new() };
    let mut out: Vec<String> = entries
        .flatten()
        .filter_map(|e| {
            let path = e.path();
            if path.extension()? != "lean" {
                return None;
            }
            let stem = path.file_stem()?.to_str()?;
            dir.join(stem).is_dir().then(|| stem.to_owned())
        })
        .collect();
    out.sort();
    out
}

/// The path with `.` components and symlinks resolved, or the path itself when
/// it does not exist — a configured source that was never fetched is not a
/// reason to report every package as unindexed.
fn real(p: &Path) -> PathBuf {
    std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// Whether the directory looks like a lake project at all, so the failure is
/// reported before a minute of Mathlib loading rather than after.
pub fn is_lake_project(dir: &Path) -> bool {
    dir.join("lakefile.toml").is_file() || dir.join("lakefile.lean").is_file()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::application::ports::Missing;

    #[test]
    fn the_shipped_script_still_has_its_markers() {
        assert!(DUMP_LEAN.contains(BEGIN) && DUMP_LEAN.contains(END));
    }

    #[test]
    fn splicing_replaces_the_import_block_and_keeps_the_rest() {
        let out = splice_imports(DUMP_LEAN, "Transformer").unwrap();
        assert!(out.contains("import Transformer"));
        assert!(!out.contains("\nimport Mathlib\n"), "the placeholder import is gone");
        assert!(out.contains("Discrtree.dumpAll"), "the body survived");
        assert!(out.contains(END));
    }

    #[test]
    fn splicing_twice_is_idempotent() {
        let once = splice_imports(DUMP_LEAN, "Mathlib").unwrap();
        assert_eq!(splice_imports(&once, "Mathlib").unwrap(), once);
    }

    #[test]
    fn a_script_without_markers_is_reported_not_silently_mangled() {
        assert!(splice_imports("import Mathlib\n#eval 1", "X").is_err());
    }

    /// A project whose `.lake/packages` holds `mathlib` and `batteries`, with
    /// only the first configured as a source.
    fn project(name: &str) -> Config {
        let root = std::env::temp_dir().join(name);
        let _ = std::fs::remove_dir_all(&root);
        for (pkg, lib) in [("mathlib", "Mathlib"), ("batteries", "Batteries")] {
            let dir = root.join(PACKAGES).join(pkg);
            std::fs::create_dir_all(dir.join(lib)).unwrap();
            std::fs::write(dir.join(format!("{lib}.lean")), "").unwrap();
        }
        Config::parse(CONFIG, &root).unwrap()
    }

    /// Mathlib configured, batteries resolved and not, and nothing that imports
    /// a root of core.
    const CONFIG: &str = r#"
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
"#;

    #[test]
    fn a_configured_package_is_not_reported_and_the_rest_are() {
        let cfg = project("dt-packages-listed");
        let found = LakeBuild::read(&cfg).unindexed();
        assert_eq!(found.len(), 1, "{found:?}");
        assert_eq!(found[0].name, "batteries");
        assert_eq!(found[0].roots, vec!["Batteries".to_string()]);
    }

    #[test]
    fn the_source_path_matches_the_package_through_a_dot_component() {
        // `root = "."` makes every configured path `<base>/./.lake/packages/x`
        // while the directory walk produces `<base>/.lake/packages/x`. Comparing
        // them as written would report Mathlib itself as unindexed.
        let cfg = project("dt-packages-dot");
        assert!(LakeBuild::read(&cfg).module("Mathlib.Analysis").is_none());
        assert_eq!(
            LakeBuild::read(&cfg).module("Batteries.Data.RBMap"),
            Some(Missing::Package("batteries".into()))
        );
    }

    #[test]
    fn a_project_with_no_packages_directory_reports_nothing() {
        let root = std::env::temp_dir().join("dt-packages-absent");
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        let cfg = Config::parse(
            "[project]\nroot = \".\"\nsrc = \"src\"\nnamespace = \"T\"\n\
             imports = \"src/T.lean\"\nvendor = \"src/T/V\"\n",
            &root,
        )
        .unwrap();
        assert!(LakeBuild::read(&cfg).unindexed().is_empty());
    }

    /// The toolchain is read off the file the project pins it in, and "core is
    /// indexed" off what a source imports rather than where it points: a dump
    /// of core has to say `import Init`, while the path may be elan, a source
    /// tarball or a checkout of lean4.
    #[test]
    fn the_toolchain_is_named_and_an_unindexed_core_is_reported_as_such() {
        let cfg = project("dt-core-toolchain");
        std::fs::write(cfg.root().join(TOOLCHAIN), "leanprover/lean4:v4.33.1\n").unwrap();
        let tc = LakeBuild::read(&cfg).toolchain().expect("the file is there");
        assert_eq!(tc.name, "leanprover/lean4:v4.33.1");
        assert!(!tc.indexed, "no source imports Init");
        assert_eq!(
            LakeBuild::read(&cfg).declaring("Int.add_one_le_iff"),
            Some(Missing::Core("leanprover/lean4:v4.33.1".into()))
        );
    }

    #[test]
    fn a_source_that_imports_a_core_root_is_core_indexed() {
        let cfg = project("dt-core-indexed");
        std::fs::write(cfg.root().join(TOOLCHAIN), "leanprover/lean4:v4.33.1\n").unwrap();
        let with_core = format!(
            "{CONFIG}\n[[source]]\nname = \"core\"\nkind = \"lake\"\n\
             path = \".lake/packages/nowhere\"\nroot = \"Init\"\n"
        );
        let cfg = Config::parse(&with_core, &cfg.root()).unwrap();
        assert!(LakeBuild::read(&cfg).toolchain().unwrap().indexed);
        assert!(LakeBuild::read(&cfg).declaring("Int.add_one_le_iff").is_none());
    }

    /// The kind that exists so nobody has to know the trick above: a `core`
    /// source names no module at all, and the module it imports is filled in
    /// from what Lean is rather than from what the reader typed.
    #[test]
    fn a_core_source_needs_no_root_to_count_as_core_indexed() {
        let cfg = project("dt-core-kind");
        std::fs::write(cfg.root().join(TOOLCHAIN), "leanprover/lean4:v4.33.1\n").unwrap();
        let with_core = format!("{CONFIG}\n[[source]]\nname = \"core\"\nkind = \"core\"\n");
        let cfg = Config::parse(&with_core, &cfg.root()).unwrap();
        assert!(LakeBuild::read(&cfg).toolchain().unwrap().indexed);
        assert!(LakeBuild::read(&cfg).declaring("Int.add_one_le_iff").is_none());
        assert!(LakeBuild::read(&cfg).module("Init.Data.Int.Order").is_none());
    }

    /// The one piece of elan's layout this relies on, pinned so that a change
    /// to it is a failing test rather than a `dt show` that quietly stops
    /// printing core's source text.
    #[test]
    fn a_toolchain_name_is_a_directory_name_with_its_separators_folded() {
        assert_eq!(elan_dir_name("leanprover/lean4:v4.33.1"), "leanprover--lean4---v4.33.1");
        assert_eq!(elan_dir_name("stable"), "stable");
    }

    /// A project that pins no toolchain is not one this can speak about, and
    /// says nothing rather than guessing.
    #[test]
    fn no_toolchain_file_means_no_claim_about_core() {
        let cfg = project("dt-core-unpinned");
        assert!(LakeBuild::read(&cfg).toolchain().is_none());
        assert!(LakeBuild::read(&cfg).declaring("Int.add_one_le_iff").is_none());
    }

    #[test]
    fn a_library_is_a_lean_file_beside_a_directory_of_the_same_name() {
        let dir = std::env::temp_dir().join("dt-packages-roots");
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("Batteries")).unwrap();
        std::fs::write(dir.join("Batteries.lean"), "").unwrap();
        // A test directory with no root module, and a script with no directory:
        // neither is something an `import` can reach.
        std::fs::create_dir_all(dir.join("BatteriesTest")).unwrap();
        std::fs::write(dir.join("scripts.lean"), "").unwrap();
        std::fs::write(dir.join("README.md"), "").unwrap();
        assert_eq!(roots(&dir), vec!["Batteries".to_string()]);
    }
}
