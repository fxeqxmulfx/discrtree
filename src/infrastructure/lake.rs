//! Phase 1 through a process boundary.
//!
//! Only the elaborator can read `.olean` and hand back an elaborated type with
//! notation expanded — without it a sum never becomes `Finset.sum` and shape
//! search has no ground to stand on. So the dump is Lean, and this is the whole
//! of the Rust side's knowledge of it: splice the right imports into
//! `lean/dump.lean`, set four environment variables, run `lake env lean`.

use crate::application::ports::{DumpSpec, Elaborator};
use crate::error::{Error, Result, bail};
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
}
