//! `dt status` — what is indexed, and whether it can be trusted.
//!
//! "Can be trusted" is the part that needs more than a row count. An index is
//! a snapshot, and a snapshot that has silently fallen behind the library is
//! worse than no index: it answers confidently with an import line that no
//! longer resolves. So every source reports the revision it was built from
//! alongside the revision it would be built from now.

use crate::application::ports::{DeclRepo, Revisions, Workspace};
use crate::domain::source::SourceKind;
use crate::error::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceStatus {
    pub name: String,
    pub kind: SourceKind,
    pub elaborated: bool,
    pub importable: bool,
    pub decls: usize,
    /// The revision the index was built from, when the index remembers.
    pub indexed_rev: Option<String>,
    /// The revision the source is at on disk now.
    pub current_rev: Option<String>,
    /// How long ago it was indexed, in seconds.
    pub age: Option<u64>,
}

impl SourceStatus {
    /// Whether the source has moved since it was indexed. Unknown counts as
    /// not stale: reporting a revision nobody could read as a mismatch would
    /// cry wolf on every source that is a plain directory.
    pub fn stale(&self) -> bool {
        match (&self.indexed_rev, &self.current_rev) {
            (Some(was), Some(now)) => was != now,
            _ => false,
        }
    }
}

pub struct Status<'a> {
    pub repo: &'a dyn DeclRepo,
    pub revisions: &'a dyn Revisions,
    pub workspace: &'a Workspace,
    /// Now, in seconds since the Unix epoch.
    pub now: u64,
}

impl Status<'_> {
    pub fn run(&self) -> Result<Vec<SourceStatus>> {
        let counts = self.repo.counts()?;
        let mut out = Vec::new();
        for s in self.workspace.sources.iter() {
            let was = self.repo.provenance(&s.id)?;
            out.push(SourceStatus {
                name: s.id.to_string(),
                kind: s.kind,
                elaborated: s.elaborated,
                importable: s.importable,
                decls: counts.iter().find(|(id, _)| id == &s.id).map_or(0, |(_, n)| *n),
                indexed_rev: was.as_ref().and_then(|p| p.revision.clone()),
                current_rev: self.revisions.current(&s.id)?,
                age: was.map(|p| self.now.saturating_sub(p.indexed_at)),
            });
        }
        Ok(out)
    }
}
