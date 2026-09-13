//! `dt status` — what is indexed, and whether it can be trusted.
//!
//! "Can be trusted" is the part that needs more than a row count. An index is
//! a snapshot, and a snapshot that has silently fallen behind the library is
//! worse than no index: it answers confidently with an import line that no
//! longer resolves. So every source reports the revision it was built from
//! alongside the revision it would be built from now.

use crate::application::ports::{DeclRepo, Revisions, Workspace};
use crate::domain::source::{SourceId, SourceKind};
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
    /// Whether the source has moved since it was indexed.
    pub fn stale(&self) -> bool {
        moved(&self.indexed_rev, &self.current_rev)
    }
}

/// Two revisions disagree only when both are known. Unknown counts as not
/// stale: reporting a revision nobody could read as a mismatch would cry wolf
/// on every source that is a plain directory.
fn moved(was: &Option<String>, now: &Option<String>) -> bool {
    matches!((was, now), (Some(was), Some(now)) if was != now)
}

/// Which of these sources have moved since they were indexed.
///
/// The same comparison `dt status` reports, minus the row counts — and that is
/// the point of it existing separately. This runs on every search, so that a
/// search whose answer a stale index has corrupted says so; `counts()` is a
/// `GROUP BY` over every row in the index, and paying it to print a line that
/// is usually empty is how a warning earns its way back out of a tool.
///
/// Nothing here is fatal. A source whose revision cannot be read is not stale,
/// which is the same rule [`SourceStatus::stale`] follows and for the same
/// reason: the cost of a false alarm is that the next real one is ignored.
pub fn stale_among(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    among: impl IntoIterator<Item = SourceId>,
) -> Result<Vec<SourceId>> {
    let mut out = Vec::new();
    for id in among {
        let was = repo.provenance(&id)?.and_then(|p| p.revision);
        if moved(&was, &revisions.current(&id)?) {
            out.push(id);
        }
    }
    Ok(out)
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
