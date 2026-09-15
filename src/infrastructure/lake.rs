//! Phase 1 through a process boundary.
//!
//! Only the elaborator can read `.olean` and hand back an elaborated type with
//! notation expanded — without it a sum never becomes `Finset.sum` and shape
//! search has no ground to stand on. So the dump is Lean, and this is the whole
//! of the Rust side's knowledge of it: splice the right imports into
//! `lean/dump.lean`, set four environment variables, run `lake env lean`.

use crate::application::ports::{DumpSpec, Elaborator, Package, Packages};
use crate::error::{Error, Result, bail};
use crate::infrastructure::config::Config;
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
pub struct LakePackages {
    dir: PathBuf,
    /// The package directories the configured sources point at, canonical, so
    /// that `.lake/packages/mathlib` and `./.lake/packages/mathlib` are one
    /// directory rather than two.
    indexed: Vec<PathBuf>,
}

impl LakePackages {
    pub fn read(cfg: &Config) -> LakePackages {
        let indexed = cfg
            .sources
            .iter()
            .filter_map(|s| s.path.as_ref())
            .map(|p| real(&cfg.resolve(p)))
            .collect();
        LakePackages { dir: cfg.root().join(PACKAGES), indexed }
    }
}

impl Packages for LakePackages {
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
        let text = r#"
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
        Config::parse(text, &root).unwrap()
    }

    #[test]
    fn a_configured_package_is_not_reported_and_the_rest_are() {
        let cfg = project("dt-packages-listed");
        let found = LakePackages::read(&cfg).unindexed();
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
        assert!(LakePackages::read(&cfg).providing("Mathlib.Analysis").is_none());
        assert_eq!(
            LakePackages::read(&cfg).providing("Batteries.Data.RBMap").unwrap().name,
            "batteries"
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
        assert!(LakePackages::read(&cfg).unindexed().is_empty());
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
