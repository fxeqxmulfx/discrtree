//! Where a source is right now, as opposed to where the index remembers it.
//!
//! Three different places hold the answer and none of them is the index. A text
//! corpus is a checkout, so git knows. A lake dependency is not checked out by
//! us at all — the build resolved it, and `lake-manifest.json` is the record of
//! what it resolved to. Reading the manifest rather than the dependency's own
//! directory is deliberate: the manifest is what the next `lake build` will
//! honour, so it is the revision the project actually compiles against.
//!
//! Core is pinned too, and by a file in the project: `lean-toolchain` is what
//! `elan` resolves before anything is built, so the toolchain name is core's
//! revision. A bump to it is a different core, and one that has to be dumped
//! again -- which is exactly what a revision is for.
//!
//! The project itself has neither. Nobody pins it, and its working tree is
//! ahead of its last commit by definition — that is what working on it means.
//! What a dump of it actually reads is the build, so the build is what gets
//! fingerprinted: see [`build_stamp`].

use crate::application::ports::Revisions;
use crate::domain::name::ModuleName;
use crate::domain::source::SourceId;
use crate::error::Result;
use crate::infrastructure::config::{Config, Kind};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub struct OnDisk {
    /// Source → its checkout, for the sources that have one.
    pub checkouts: BTreeMap<SourceId, PathBuf>,
    /// Source → the build tree a dump of it reads, for the sources compiled
    /// here rather than resolved by a manifest.
    pub builds: BTreeMap<SourceId, PathBuf>,
    /// Package name → revision, from `lake-manifest.json`.
    pub manifest: BTreeMap<String, String>,
    /// Source → the toolchain it ships with, for the core sources.
    pub toolchains: BTreeMap<SourceId, String>,
}

impl OnDisk {
    pub fn read(cfg: &Config) -> OnDisk {
        let of_kind = |k: Kind| -> Vec<SourceId> {
            cfg.sources
                .iter()
                .filter(|s| s.kind == k)
                .map(|s| SourceId::new(s.name.clone()))
                .collect()
        };
        let checkouts = cfg
            .sources
            .iter()
            .filter(|s| s.kind == Kind::Git)
            .map(|s| (SourceId::new(s.name.clone()), cfg.source_dir(s)))
            .collect();
        // One build tree, however many local sources name it. `lake build`
        // writes the whole project into it, so a local source is stale exactly
        // when the project has been rebuilt since it was dumped — which is the
        // same fact for all of them.
        let lib = cfg.root().join(BUILD_LIB);
        let builds = of_kind(Kind::Local).into_iter().map(|id| (id, lib.clone())).collect();
        let toolchain = cfg.toolchain();
        let toolchains = of_kind(Kind::Core)
            .into_iter()
            .filter_map(|id| toolchain.clone().map(|t| (id, t)))
            .collect();
        OnDisk {
            checkouts,
            builds,
            manifest: manifest(&cfg.root().join("lake-manifest.json")),
            toolchains,
        }
    }
}

impl Revisions for OnDisk {
    fn current(&self, source: &SourceId) -> Result<Option<String>> {
        if let Some(dir) = self.checkouts.get(source) {
            return Ok(head(dir));
        }
        if let Some(lib) = self.builds.get(source) {
            return Ok(build_stamp(lib));
        }
        if let Some(toolchain) = self.toolchains.get(source) {
            return Ok(Some(toolchain.clone()));
        }
        Ok(self.manifest.get(source.as_str()).cloned())
    }

    /// By the module's `.olean`, which a build rewrites exactly when it
    /// compiles the module. Lake has written them under `lib/lean` and, before
    /// that, straight under `lib`; whichever exists is the one it reads.
    fn rebuilt_since(&self, source: &SourceId, module: &ModuleName, since: u64) -> Option<bool> {
        let lib = self.builds.get(source)?;
        let rel: PathBuf = module.as_str().split('.').collect::<PathBuf>().with_extension("olean");
        [lib.join("lean").join(&rel), lib.join(&rel)].iter().find_map(|p| {
            let t = std::fs::metadata(p).ok()?.modified().ok()?;
            let secs = t.duration_since(std::time::UNIX_EPOCH).ok()?.as_secs();
            Some(secs > since)
        })
    }
}

/// Where `lake build` puts the `.olean` files, relative to the project root.
const BUILD_LIB: &str = ".lake/build/lib";

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

/// A revision for a source that nobody pins: a fingerprint of the build a dump
/// of it would read.
///
/// A git SHA and this are the same kind of thing — a short value that changes
/// when the source changes and not otherwise — and they are compared the same
/// way, so the project gets the staleness reporting the other sources already
/// had. It has to be the build rather than the `.lean` files, because the build
/// is what `dt dump` reads: an edited file that has not been compiled yet would
/// otherwise call the index stale when re-dumping it would change nothing.
///
/// Over `(module path, size, mtime)` rather than the bytes: the whole point is
/// to be cheap enough to recompute on every `dt status` and every search, and
/// hashing a few hundred megabytes of `.olean` is not. This is the same trade
/// as [`file_stamp`], and it is Lake's own: a rebuild rewrites the file, and a
/// rewritten file gets a new mtime.
///
/// `None` when the project has not been built — an unbuilt tree has no revision
/// in the same sense that a directory which is not a checkout has none, and
/// saying so is what keeps [`crate::application::status::SourceStatus::stale`]
/// from crying wolf.
pub fn build_stamp(lib: &Path) -> Option<String> {
    let mut entries = Vec::new();
    oleans(lib, lib, &mut entries);
    if entries.is_empty() {
        return None;
    }
    // Sorted because a directory listing is in whatever order the filesystem
    // hands it back, and two walks of an unchanged tree must agree.
    entries.sort_unstable();
    let mut h = Fnv::new();
    for (path, len, mtime) in &entries {
        h.write(path.as_bytes());
        h.write(&len.to_le_bytes());
        h.write(&mtime.to_le_bytes());
    }
    Some(format!("{:016x}", h.0))
}

/// Every `.olean` under `dir`, as (path relative to `root`, size, mtime).
/// An unreadable directory or file contributes nothing rather than failing:
/// this feeds a warning, and a warning that aborts a search is worse than the
/// staleness it was reporting.
fn oleans(root: &Path, dir: &Path, out: &mut Vec<(String, u64, u64)>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        match entry.file_type() {
            Ok(t) if t.is_dir() => oleans(root, &path, out),
            Ok(t) if t.is_file() && path.extension().is_some_and(|e| e == "olean") => {
                let Ok(m) = entry.metadata() else { continue };
                let mtime = m
                    .modified()
                    .ok()
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map_or(0, |d| d.as_secs());
                let rel = path.strip_prefix(root).unwrap_or(&path);
                out.push((rel.to_string_lossy().into_owned(), m.len(), mtime));
            }
            _ => {}
        }
    }
}

/// FNV-1a, 64 bits. Hand-written because the alternative is a dependency, and
/// a dependency is too much to pay for the one thing asked of it here: that two
/// different build trees get two different short strings. Nothing security-
/// shaped rests on this — a collision would report a stale index as current,
/// the same failure as not looking at all, and at one in 2^64.
struct Fnv(u64);

impl Fnv {
    fn new() -> Fnv {
        Fnv(0xcbf2_9ce4_8422_2325)
    }

    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 ^= u64::from(*b);
            self.0 = self.0.wrapping_mul(0x1000_0000_01b3);
        }
    }
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
    use crate::infrastructure::lake;

    /// Core moves when the toolchain moves and at no other time, so the
    /// toolchain name is its revision. Without this a core source has no
    /// revision at all, which reads as "nothing is known" -- and an index of
    /// v4.33.1 core would go on answering v4.34 questions without a word.
    #[test]
    fn a_core_source_is_at_whatever_the_toolchain_says() {
        let dir = std::env::temp_dir().join("dt-core-revision-test");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(lake::TOOLCHAIN), "leanprover/lean4:v4.33.1\n").unwrap();
        let text = r#"
[project]
root = "."
src = "src"
namespace = "T"
imports = "src/T.lean"
vendor = "src/T/Vendor"

[[source]]
name = "core"
kind = "core"
"#;
        let cfg = Config::parse(text, &dir).unwrap();
        let revs = OnDisk::read(&cfg);
        assert_eq!(
            revs.current(&SourceId::new("core")).unwrap().as_deref(),
            Some("leanprover/lean4:v4.33.1")
        );
        // A project with no `lean-toolchain` says nothing rather than guessing.
        let bare = std::env::temp_dir().join("dt-core-revision-bare");
        std::fs::create_dir_all(&bare).unwrap();
        let cfg = Config::parse(text, &bare).unwrap();
        assert_eq!(OnDisk::read(&cfg).current(&SourceId::new("core")).unwrap(), None);
    }

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

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(name);
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn olean(lib: &Path, rel: &str, contents: &str) {
        let path = lib.join(rel);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, contents).unwrap();
    }

    /// The property the whole warning rests on: the same build hashes the same
    /// and a rebuilt one does not. Size is enough to show the second half
    /// without waiting for the clock to tick.
    #[test]
    fn a_build_stamp_moves_when_the_build_does() {
        let lib = scratch("dt-build-stamp");
        olean(&lib, "lean/Transformer.olean", "aa");
        olean(&lib, "lean/Transformer/Hull.olean", "bb");
        let before = build_stamp(&lib).unwrap();
        assert_eq!(build_stamp(&lib).as_deref(), Some(before.as_str()));

        olean(&lib, "lean/Transformer/Hull.olean", "bbb");
        assert_ne!(build_stamp(&lib).as_deref(), Some(before.as_str()));
    }

    /// A module compiled since the last dump is exactly the case `dt status`
    /// could not see, so adding one has to move the stamp even though no
    /// existing file was touched.
    #[test]
    fn a_new_module_moves_the_build_stamp() {
        let lib = scratch("dt-build-stamp-new");
        olean(&lib, "lean/Transformer.olean", "aa");
        let before = build_stamp(&lib).unwrap();
        olean(&lib, "lean/Transformer/HullProbe.olean", "cc");
        assert_ne!(build_stamp(&lib).as_deref(), Some(before.as_str()));
    }

    /// An unbuilt project has no revision, the same as a directory that is not
    /// a checkout. It must not get an empty-walk fingerprint, which would be a
    /// value that compares equal to the next empty walk and so would read as
    /// "up to date" forever.
    #[test]
    fn an_unbuilt_project_has_no_revision() {
        assert!(build_stamp(Path::new("/nonexistent/.lake/build/lib")).is_none());
        assert!(build_stamp(&scratch("dt-build-stamp-empty")).is_none());
    }

    /// The layout of the build tree changed between Lake versions — `lib/Foo`
    /// then `lib/lean/Foo` — so the walk is over everything below `lib` rather
    /// than a path the tool thinks it knows. Getting that wrong yields no
    /// files, which is indistinguishable from an unbuilt project.
    #[test]
    fn either_build_layout_is_fingerprinted() {
        let old = scratch("dt-build-stamp-old-layout");
        olean(&old, "Transformer/Hull.olean", "aa");
        assert!(build_stamp(&old).is_some());
    }

    /// A local source is fingerprinted by the project build; a lake dependency
    /// keeps the manifest revision, which says what upstream it is rather than
    /// what this machine compiled.
    #[test]
    fn a_local_source_gets_the_build_and_a_lake_source_the_manifest() {
        let root = scratch("dt-revisions-local");
        olean(&root.join(BUILD_LIB), "lean/Transformer.olean", "aa");
        std::fs::write(
            root.join("lake-manifest.json"),
            r#"{"packages":[{"name":"mathlib","rev":"0df444a3"}]}"#,
        )
        .unwrap();
        let cfg = Config::parse(
            &format!(
                "[project]\nroot = \"{}\"\nsrc = \"src\"\nnamespace = \"T\"\n\
                 imports = \"src/T.lean\"\nvendor = \"src/T/Vendor\"\n\
                 [[source]]\nname = \"project\"\nkind = \"local\"\nroot = \"T\"\n\
                 [[source]]\nname = \"mathlib\"\nkind = \"lake\"\nroot = \"Mathlib\"\n",
                root.display()
            ),
            Path::new("/unused"),
        )
        .unwrap();
        let revs = OnDisk::read(&cfg);
        let project = revs.current(&SourceId::new("project")).unwrap();
        assert_eq!(project, build_stamp(&root.join(BUILD_LIB)));
        assert!(project.is_some(), "the project build is a revision like any other");
        assert_eq!(revs.current(&SourceId::new("mathlib")).unwrap().as_deref(), Some("0df444a3"));
    }
}
