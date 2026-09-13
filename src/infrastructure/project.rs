//! The filesystem: reading the corpora, and the one adapter that writes into
//! `src/`.

use crate::application::ports::{ProjectWriter, SourceFiles};
use crate::domain::name::ModuleName;
use crate::domain::source::SourceId;
use crate::error::{Error, Result, bail};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// Where each source's `.lean` files live, and what never to read.
pub struct Files {
    pub roots: BTreeMap<SourceId, PathBuf>,
    /// Path fragments never scanned, however large the directory.
    pub excludes: BTreeMap<SourceId, Vec<String>>,
}

impl SourceFiles for Files {
    fn read_module(&self, source: &SourceId, module: &ModuleName) -> Result<String> {
        let path = self.location(source).join(module.relative_path());
        std::fs::read_to_string(&path).map_err(|e| Error::new(format!("{}: {e}", path.display())))
    }

    fn list_modules(&self, source: &SourceId) -> Result<Vec<(ModuleName, PathBuf)>> {
        let root = self.location(source);
        if !root.is_dir() {
            bail!("source `{source}` is not on disk at {}; run `dt fetch {source}`", root.display())
        }
        let excludes = self.excludes.get(source).cloned().unwrap_or_default();
        let mut out = Vec::new();
        walk(&root, &root, &excludes, &mut out)?;
        out.sort();
        Ok(out)
    }

    fn location(&self, source: &SourceId) -> PathBuf {
        self.roots.get(source).cloned().unwrap_or_else(|| PathBuf::from("."))
    }
}

fn walk(
    root: &Path,
    dir: &Path,
    excludes: &[String],
    out: &mut Vec<(ModuleName, PathBuf)>,
) -> Result<()> {
    // A build directory holds copies of everything and would double the corpus.
    const NEVER: &[&str] = &[".git", ".lake", "build", "node_modules"];
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return Ok(()),
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        if NEVER.contains(&name.as_str()) || excludes.contains(&name) {
            continue;
        }
        if path.is_dir() {
            walk(root, &path, excludes, out)?;
        } else if path.extension().is_some_and(|e| e == "lean") {
            let rel = path.strip_prefix(root).unwrap_or(&path);
            if excludes.iter().any(|x| rel.to_string_lossy().contains(x.as_str())) {
                continue;
            }
            if let Some(m) = ModuleName::from_relative_path(rel) {
                out.push((m, path));
            }
        }
    }
    Ok(())
}

/// Writing into `src/`. The aggregator is edited in place, because a module not
/// reachable from it is not built.
pub struct Project {
    /// The aggregator, e.g. `src/Transformer.lean`.
    pub imports_file: PathBuf,
}

impl ProjectWriter for Project {
    fn write_module(&mut self, path: &Path, contents: &str, force: bool) -> Result<()> {
        if path.exists() && !force {
            bail!("{} already exists; re-run with --force to replace it", path.display())
        }
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(path, contents)
            .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
        Ok(())
    }

    fn add_imports(&mut self, modules: &[ModuleName]) -> Result<Vec<ModuleName>> {
        if modules.is_empty() {
            return Ok(Vec::new());
        }
        let text = std::fs::read_to_string(&self.imports_file)
            .map_err(|e| Error::new(format!("{}: {e}", self.imports_file.display())))?;
        let added = insert_imports(&text, modules);
        if added.text != text {
            std::fs::write(&self.imports_file, &added.text)
                .map_err(|e| Error::new(format!("{}: {e}", self.imports_file.display())))?;
        }
        Ok(added.added)
    }
}

pub struct Inserted {
    pub text: String,
    pub added: Vec<ModuleName>,
}

/// Add import lines after the last existing one, skipping any already there.
/// Kept pure so the aggregator edit is testable without touching a project.
pub fn insert_imports(text: &str, modules: &[ModuleName]) -> Inserted {
    let lines: Vec<&str> = text.lines().collect();
    let present: Vec<&str> =
        lines.iter().filter_map(|l| l.trim().strip_prefix("import ")).map(str::trim).collect();
    let added: Vec<ModuleName> =
        modules.iter().filter(|m| !present.contains(&m.as_str())).cloned().collect();
    if added.is_empty() {
        return Inserted { text: text.to_string(), added };
    }
    let last_import = lines.iter().rposition(|l| l.trim_start().starts_with("import "));
    let at = last_import.map_or(0, |i| i + 1);
    let mut out: Vec<String> = lines[..at].iter().map(|s| s.to_string()).collect();
    out.extend(added.iter().map(ModuleName::import_line));
    out.extend(lines[at..].iter().map(|s| s.to_string()));
    let mut text = out.join("\n");
    text.push('\n');
    Inserted { text, added }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imports_go_after_the_last_existing_one() {
        let before = "import Mathlib\nimport Transformer.Basic\n\n/-! docs -/\n";
        let got = insert_imports(before, &[ModuleName::new("Transformer.Vendor.Flt.A")]);
        assert_eq!(
            got.text,
            "import Mathlib\nimport Transformer.Basic\nimport Transformer.Vendor.Flt.A\n\n/-! docs -/\n"
        );
        assert_eq!(got.added.len(), 1);
    }

    #[test]
    fn an_import_already_there_is_not_repeated() {
        let before = "import Mathlib\n";
        let got = insert_imports(before, &[ModuleName::new("Mathlib")]);
        assert_eq!(got.text, before);
        assert!(got.added.is_empty());
    }

    #[test]
    fn a_file_with_no_imports_gets_them_at_the_top() {
        let got = insert_imports("/-! just docs -/\n", &[ModuleName::new("A")]);
        assert!(got.text.starts_with("import A\n"));
    }
}
