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

use crate::application::ports::{
    Build, DeclRepo, Located, Package, Provenance, Revisions, Toolchain, Workspace,
};
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::source::{SourceId, SourceKind};
use crate::error::Result;
use std::collections::{BTreeMap, BTreeSet};

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
    /// The `dt` that wrote these rows, when it is not the one reading them.
    /// `Some(None)` is a `dt` too old to have recorded which it was.
    pub written_by: Option<Option<String>>,
}

impl SourceStatus {
    /// Whether the index can be trusted for this source: whether the source has
    /// moved since it was indexed, and whether the rows were written by a `dt`
    /// that wrote them differently. Either one makes the answers wrong rather
    /// than late, which is what the column cannot show and this has to.
    pub fn stale(&self) -> bool {
        moved(&self.indexed_rev, &self.current_rev) || self.written_by.is_some()
    }
}

/// Two revisions disagree only when both are known. Unknown counts as not
/// stale: reporting a revision nobody could read as a mismatch would cry wolf
/// on every source that is a plain directory.
fn moved(was: &Option<String>, now: &Option<String>) -> bool {
    matches!((was, now), (Some(was), Some(now)) if was != now)
}

/// A source the index has fallen behind, and what it fell behind.
///
/// The reason is carried rather than reduced to a flag, because one value alone
/// is not believable. "`project` moved since it was indexed" was read as a
/// claim about a path -- which had not moved -- and filed as a bug in the
/// check; what had changed was the build the project was dumped from, and
/// saying which value differs is what makes the line something a reader can
/// check rather than argue with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Stale {
    pub id: SourceId,
    pub why: Why,
}

/// The two ways an index falls behind, which are not the same fact and do not
/// have the same repair.
///
/// A source that moved has to be read again — dumped, fetched — before it can
/// be indexed. A source whose rows were written by an older `dt` has not moved:
/// the dump on disk is the right dump, and re-reading it from Lean would cost
/// an hour to produce the bytes that are already there. Only the load has to
/// run again. Keeping the distinction here is what lets `dt refresh` charge the
/// cheap price when the cheap price is the right one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Why {
    /// Indexed at one revision, on disk at another.
    Moved { indexed: String, current: String },
    /// The rows are in an older row format. `by` is the `dt` that wrote them,
    /// when it recorded which it was.
    Written { by: Option<String> },
}

impl Why {
    /// Whether the source itself has to be read again, or only re-indexed.
    pub fn needs_reread(&self) -> bool {
        matches!(self, Why::Moved { .. })
    }
}

/// Which of these sources the index has fallen behind, and how.
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
) -> Result<Vec<Stale>> {
    let mut out = Vec::new();
    for id in among {
        let Some(was) = repo.provenance(&id)? else { continue };
        let now = revisions.current(&id)?;
        // A source that has moved *and* holds old rows is reported as moved:
        // it needs the re-read, and the load that follows it is the other
        // repair anyway.
        if let (true, Some(indexed), Some(current)) =
            (moved(&was.revision, &now), &was.revision, now)
        {
            out.push(Stale { id, why: Why::Moved { indexed: indexed.clone(), current } });
        } else if was.outdated() {
            out.push(Stale { id, why: Why::Written { by: was.writer } });
        }
    }
    Ok(out)
}

/// The sources whose revision moved while they were being read.
///
/// `before` is each source's revision as the read began; the index records
/// that one, since it is the build the read started from. A build that
/// finishes in the minutes a dump takes -- a `lake build` still running, the
/// editor compiling an import -- leaves the index behind the moment the refresh
/// ends, and the next search saying "rebuilt since it was indexed" about a
/// refresh that just finished reads as a bug in the refresh. Said here, at the
/// end of the refresh, it is the explanation instead.
pub fn moved_while_read(
    revisions: &dyn Revisions,
    before: &BTreeMap<SourceId, Option<String>>,
) -> Result<Vec<Stale>> {
    let mut out = Vec::new();
    for (id, was) in before {
        let now = revisions.current(id)?;
        if let (true, Some(indexed), Some(current)) = (moved(was, &now), was, now) {
            out.push(Stale {
                id: id.clone(),
                why: Why::Moved { indexed: indexed.clone(), current },
            });
        }
    }
    Ok(out)
}

/// [`stale_among`], for a search: the sources whose rows may be missing.
///
/// A project is rebuilt after nearly every edit, and a line after every search
/// that said so went unread by the time it mattered, while a refresh after
/// every build is too slow to ask for. What a search can miss is a declaration
/// the build has and the index does not, so a rebuilt project is let off when
/// every declaration of every module compiled since it was indexed has a row,
/// at the lines the build gives it, spelled as the source spells it there. A
/// new, renamed, moved or restated declaration keeps the line; an edited proof
/// does not.
pub fn stale_for_search(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    among: impl IntoIterator<Item = SourceId>,
) -> Result<Vec<Stale>> {
    let mut kept = Vec::new();
    for s in stale_among(repo, revisions, among)? {
        if !indexed_as_built(repo, revisions, &s)? {
            kept.push(s);
        }
    }
    Ok(kept)
}

/// Whether a source that moved only rebuilt what the index already holds.
fn indexed_as_built(repo: &dyn DeclRepo, revisions: &dyn Revisions, s: &Stale) -> Result<bool> {
    if !matches!(s.why, Why::Moved { .. }) {
        return Ok(false);
    }
    let Some(was) = repo.provenance(&s.id)? else { return Ok(false) };
    let Some(declared) = revisions.declared_since(&s.id, was.indexed_at) else {
        return Ok(false);
    };
    // A build that moved and compiled nothing since has changed in a way the
    // modules cannot show -- a file deleted, or compiled while it was dumped.
    if declared.is_empty() {
        return Ok(false);
    }
    for (module, decls) in &declared {
        let Some(rows) = repo.located_in(&s.id, module)? else { return Ok(false) };
        let indexed = |(name, built): (&DeclName, &Located)| {
            built.span.is_some() && built.statement.is_some() && rows.get(name) == Some(built)
        };
        if !decls.iter().all(indexed) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// [`stale_among`], for a command that printed these rows and nothing else.
///
/// A rebuilt project is stale as a source, and "rows may be missing" is true
/// of a search over it. It is not true of `dt show`: the row it printed is
/// there, and it is out of date only if its own module was compiled again.
/// After a build that touched four modules, every `show` of a declaration in
/// the other hundred ended in a warning about it -- a line that is wrong most
/// of the time is a line nobody reads the time it is right. So a source whose
/// build moved is let off when each module shown is known not to have been
/// rebuilt since the index was written, or when the index holds what the
/// rebuild declares, as [`stale_for_search`] decides.
pub fn stale_for_rows(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    rows: &BTreeMap<SourceId, BTreeSet<ModuleName>>,
) -> Result<Vec<Stale>> {
    let mut out = stale_among(repo, revisions, rows.keys().cloned())?;
    let mut kept = Vec::with_capacity(out.len());
    for s in out.drain(..) {
        let untouched = matches!(s.why, Why::Moved { .. })
            && match repo.provenance(&s.id)? {
                Some(was) => rows[&s.id]
                    .iter()
                    .all(|m| revisions.rebuilt_since(&s.id, m, was.indexed_at) == Some(false)),
                None => false,
            };
        if !untouched && !indexed_as_built(repo, revisions, &s)? {
            kept.push(s);
        }
    }
    Ok(kept)
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
                age: was.as_ref().map(|p| self.now.saturating_sub(p.indexed_at)),
                written_by: was.filter(Provenance::outdated).map(|p| p.writer),
            });
        }
        Ok(Report {
            sources: out,
            unindexed: self.build.unindexed(),
            toolchain: self.build.toolchain(),
        })
    }
}
