//! Where a source is right now, as opposed to where the index remembers it.
//!
//! Two different places hold the answer and neither is the index. A text corpus
//! is a checkout, so git knows. A lake dependency is not checked out by us at
//! all — the build resolved it, and `lake-manifest.json` is the record of what
//! it resolved to. Reading the manifest rather than the dependency's own
//! directory is deliberate: the manifest is what the next `lake build` will
//! honour, so it is the revision the project actually compiles against.

use crate::application::ports::Revisions;
use crate::domain::source::SourceId;
use crate::error::Result;
use crate::infrastructure::config::{Config, Kind};
use std::collections::BTreeMap;
use std::path::Path;

pub struct OnDisk {
    /// Source → its checkout, for the sources that have one.
    pub checkouts: BTreeMap<SourceId, std::path::PathBuf>,
    /// Package name → revision, from `lake-manifest.json`.
    pub manifest: BTreeMap<String, String>,
}

impl OnDisk {
    pub fn read(cfg: &Config) -> OnDisk {
        let checkouts = cfg
            .sources
            .iter()
            .filter(|s| s.kind == Kind::Git)
            .map(|s| (SourceId::new(s.name.clone()), cfg.source_dir(s)))
            .collect();
        OnDisk { checkouts, manifest: manifest(&cfg.root().join("lake-manifest.json")) }
    }
}

impl Revisions for OnDisk {
    fn current(&self, source: &SourceId) -> Result<Option<String>> {
        if let Some(dir) = self.checkouts.get(source) {
            return Ok(head(dir));
        }
        Ok(self.manifest.get(source.as_str()).cloned())
    }
}

/// `git rev-parse HEAD`, or nothing. A source that is not a checkout is not an
/// error: it is a directory somebody put there, and it has no revision.
fn head(dir: &Path) -> Option<String> {
    if !dir.join(".git").exists() {
        return None;
    }
    let out = std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(dir)
        .output()
        .ok()?;
    out.status.success().then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// Package name → revision. A manifest that is missing or in a shape this does
/// not recognise yields nothing, because a wrong revision would be worse than
/// no revision: it would make a stale index look current.
fn manifest(path: &Path) -> BTreeMap<String, String> {
    let Ok(text) = std::fs::read_to_string(path) else { return BTreeMap::new() };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        return BTreeMap::new();
    };
    json.get("packages")
        .and_then(|p| p.as_array())
        .map(|ps| {
            ps.iter()
                .filter_map(|p| {
                    let name = p.get("name")?.as_str()?.to_string();
                    let rev = p.get("rev")?.as_str()?.to_string();
                    Some((name, rev))
                })
                .collect()
        })
        .unwrap_or_default()
}

/// A fingerprint of a file, for telling whether it has been rewritten since.
/// Length and modification time, which is what every build system uses and for
/// the same reason: hashing a 700 MB dump to decide whether to read it costs
/// more than reading it.
pub fn file_stamp(path: &Path) -> Option<String> {
    let m = std::fs::metadata(path).ok()?;
    let t = m.modified().ok()?.duration_since(std::time::UNIX_EPOCH).ok()?;
    Some(format!("{}:{}", m.len(), t.as_secs()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_manifest_maps_packages_to_revisions() {
        let dir = std::env::temp_dir().join("dt-manifest-test");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("lake-manifest.json");
        std::fs::write(
            &path,
            r#"{"packages":[{"name":"mathlib","rev":"0df444a3"},{"name":"aesop","rev":"3448c0bc"}]}"#,
        )
        .unwrap();
        let m = manifest(&path);
        assert_eq!(m.get("mathlib").map(String::as_str), Some("0df444a3"));
        assert_eq!(m.len(), 2);
    }

    /// A missing or unreadable manifest must not be reported as "no packages
    /// have moved". It is reported as "nothing is known", and the caller then
    /// re-indexes rather than skipping.
    #[test]
    fn an_unreadable_manifest_yields_nothing() {
        assert!(manifest(Path::new("/nonexistent/lake-manifest.json")).is_empty());
    }
}
