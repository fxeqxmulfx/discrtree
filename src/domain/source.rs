//! Where a declaration came from, and the two properties that follow from it.
//!
//! The whole design rests on one distinction, stated once and enforced
//! everywhere: compiled sources are elaborated, text sources are not.

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceId(String);

impl SourceId {
    pub fn new(s: impl Into<String>) -> Self {
        SourceId(s.into())
    }
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for SourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for SourceId {
    fn from(s: &str) -> Self {
        SourceId::new(s)
    }
}

impl From<String> for SourceId {
    fn from(s: String) -> Self {
        SourceId(s)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceKind {
    /// A lake dependency, built alongside the project.
    Lake,
    /// The project itself.
    Local,
    /// A checkout read as text. Nothing here runs Lean.
    Git,
    /// The toolchain's own library: `Init`, `Std`, `Lean`. Compiled like a
    /// lake package and importable like one, and a kind of its own because
    /// nothing else about it is the same: it has no directory under
    /// `.lake/packages`, nobody pins it in a manifest, and what it is at any
    /// moment is whatever `lean-toolchain` says.
    Core,
}

impl SourceKind {
    /// Compiled by default; a `git` source is text.
    pub fn default_elaborated(self) -> bool {
        self != SourceKind::Git
    }

    /// Reachable by an `import` line by default; a `git` source is not.
    pub fn default_importable(self) -> bool {
        self != SourceKind::Git
    }

    pub fn as_str(self) -> &'static str {
        match self {
            SourceKind::Lake => "lake",
            SourceKind::Local => "local",
            SourceKind::Git => "git",
            SourceKind::Core => "core",
        }
    }
}

/// A source as the rest of the program sees it: the two flags already resolved,
/// plus what a provenance header needs.
#[derive(Debug, Clone)]
pub struct SourceMeta {
    pub id: SourceId,
    pub kind: SourceKind,
    /// Types come from the elaborator. Decides whether shape search and exact
    /// dependencies are available.
    pub elaborated: bool,
    /// A dependency on this source collapses into one `import` line instead of
    /// being copied. This, not a depth cap, is what makes a dependency tree
    /// tractable.
    pub importable: bool,
    pub rev: Option<String>,
    pub license: Option<String>,
    pub attribution: Option<String>,
}

impl SourceMeta {
    /// A source with everything derived from its kind.
    pub fn derived(id: impl Into<SourceId>, kind: SourceKind) -> Self {
        SourceMeta {
            id: id.into(),
            kind,
            elaborated: kind.default_elaborated(),
            importable: kind.default_importable(),
            rev: None,
            license: None,
            attribution: None,
        }
    }
}

/// The set of sources in play, so that use cases can ask about any source by id
/// without carrying the config around.
#[derive(Debug, Clone, Default)]
pub struct Sources(Vec<SourceMeta>);

impl Sources {
    pub fn new(v: Vec<SourceMeta>) -> Self {
        Sources(v)
    }

    pub fn get(&self, id: &SourceId) -> Option<&SourceMeta> {
        self.0.iter().find(|s| &s.id == id)
    }

    pub fn iter(&self) -> impl Iterator<Item = &SourceMeta> {
        self.0.iter()
    }

    /// An unknown source is treated as neither elaborated nor importable: the
    /// conservative answer, because it makes `dt add` copy rather than emit an
    /// import that would not resolve.
    pub fn importable(&self, id: &SourceId) -> bool {
        self.get(id).is_some_and(|s| s.importable)
    }

    pub fn elaborated(&self, id: &SourceId) -> bool {
        self.get(id).is_some_and(|s| s.elaborated)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags_follow_from_kind() {
        let m = SourceMeta::derived("mathlib", SourceKind::Lake);
        assert!(m.elaborated && m.importable);

        // Core is read by the elaborator and reached by an `import` line,
        // like a lake package and unlike a checkout.
        let c = SourceMeta::derived("core", SourceKind::Core);
        assert!(c.elaborated && c.importable);

        let f = SourceMeta::derived("flt", SourceKind::Git);
        assert!(!f.elaborated && !f.importable);
    }

    #[test]
    fn an_unknown_source_is_neither() {
        let s = Sources::new(vec![SourceMeta::derived("mathlib", SourceKind::Lake)]);
        assert!(s.importable(&"mathlib".into()));
        assert!(!s.importable(&"nowhere".into()));
        assert!(!s.elaborated(&"nowhere".into()));
    }
}
