//! `dt status` — what is indexed, and whether it can be trusted.
//!
//! "Can be trusted" is the part that needs more than a row count. An index is
//! a snapshot, and a snapshot that has silently fallen behind the library is
//! worse than no index: it answers confidently with an import line that no
//! longer resolves. So every source reports the revision it was built from
//! alongside the revision it would be built from now.
//!
//! The other way an index misleads is by covering less than the build does, and
//! no row of that table can show it: a corpus nobody dumped has no row. So the
//! report also names the lake packages no source claims, and the toolchain,
//! whose `Init` and `Std` sit under every one of them.

use crate::application::ports::{Build, DeclRepo, Package, Revisions, Toolchain, Workspace};
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

/// What `dt status` has to say.
///
/// Two halves, and the second is not a footnote to the first: the sources
/// answer "is what I indexed still current", and `unindexed` answers "is what I
/// indexed all of it". A table of perfectly fresh sources is not evidence that
/// a search covered the corpus, and until this was reported there was no
/// command that would say so.
#[derive(Debug, Clone)]
pub struct Report {
    pub sources: Vec<SourceStatus>,
    /// Lake packages the build resolved that no source covers.
    pub unindexed: Vec<Package>,
    /// The toolchain the project builds against, and whether its own library
    /// is in the index. Reported either way: "core is indexed" answers "why
    /// did that not match" as squarely as its opposite.
    pub toolchain: Option<Toolchain>,
}

pub struct Status<'a> {
    pub repo: &'a dyn DeclRepo,
    pub revisions: &'a dyn Revisions,
    pub build: &'a dyn Build,
    pub workspace: &'a Workspace,
    /// Now, in seconds since the Unix epoch.
    pub now: u64,
}

impl Status<'_> {
    pub fn run(&self) -> Result<Report> {
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
        Ok(Report {
            sources: out,
            unindexed: self.build.unindexed(),
            toolchain: self.build.toolchain(),
        })
    }
}
