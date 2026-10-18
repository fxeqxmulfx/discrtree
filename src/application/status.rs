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
use crate::domain::query::Query;
use crate::domain::source::{SourceId, SourceKind, Sources};
use crate::error::Result;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

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
    /// How far the source's files are ahead of its build, when they declare
    /// something the index does not hold. See [`unbuilt`].
    pub ahead: Option<Ahead>,
}

impl SourceStatus {
    /// Whether the index can be trusted for this source: whether the source has
    /// moved since it was indexed, whether the rows were written by a `dt`
    /// that wrote them differently, and whether its files declare what no
    /// build has compiled. Each makes the answers wrong rather than late,
    /// which is what the columns cannot show and this has to.
    pub fn stale(&self) -> bool {
        self.reread() || self.ahead.is_some()
    }

    /// Whether `dt refresh` alone brings this source up to date: it moved, or
    /// an older `dt` wrote its rows. A source whose files are ahead of its
    /// build needs the build first.
    pub fn reread(&self) -> bool {
        moved(&self.indexed_rev, &self.current_rev) || self.written_by.is_some()
    }

    /// Whether the index is known to hold this source as it is: indexed, at a
    /// revision that can be read, and not [`SourceStatus::stale`]. `None` when
    /// that cannot be told -- never indexed, or a revision nobody can read.
    pub fn current(&self) -> Option<bool> {
        match self.stale() {
            true => Some(false),
            false => (self.indexed_rev.is_some() && self.current_rev.is_some()).then_some(true),
        }
    }
}

/// How far a source's files are ahead of its build, for `dt status`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ahead {
    /// Files the root imports that were saved after their module was last
    /// compiled, or that no build has compiled.
    pub files: usize,
    /// Of those, the ones declaring names the index does not hold there.
    pub declaring: usize,
    /// Where `lake build` has to run.
    pub project: PathBuf,
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

/// The three ways an index falls behind, which are not the same fact and do
/// not have the same repair.
///
/// A source that moved has to be read again — dumped, fetched — before it can
/// be indexed. A source whose rows were written by an older `dt` has not moved:
/// the dump on disk is the right dump, and re-reading it from Lean would cost
/// an hour to produce the bytes that are already there. Only the load has to
/// run again. Keeping the distinction here is what lets `dt refresh` charge the
/// cheap price when the cheap price is the right one.
///
/// And a source whose files are ahead of its build cannot be brought up to
/// date by `dt` at all: a dump reads the build, and the build does not have
/// them. `lake build` comes first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Why {
    /// Indexed at one revision, on disk at another.
    Moved { indexed: String, current: String },
    /// The rows are in an older row format. `by` is the `dt` that wrote them,
    /// when it recorded which it was.
    Written { by: Option<String> },
    /// `files` of the files the root imports were saved after the build last
    /// compiled them, or were never compiled, and some declare what the index
    /// does not hold. `project` is where `lake build` has to run.
    Unbuilt { files: usize, project: PathBuf },
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
///
/// Then the files a build has not caught up with, which no revision shows: see
/// [`unbuilt`]. Those come after the build's own, and a source can be behind
/// both ways at once -- rebuilt in part, and edited past the rebuild.
pub fn stale_for_search(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    among: impl IntoIterator<Item = SourceId>,
) -> Result<Vec<(Stale, Vec<Behind>)>> {
    let among: Vec<SourceId> = among.into_iter().collect();
    let mut kept = behind_build(repo, revisions, among.iter().cloned())?;
    for id in &among {
        kept.extend(unbuilt(repo, revisions, id)?);
    }
    Ok(kept)
}

/// The sources a search may be missing rows of because the build moved, and
/// what it moved to. The first half of [`stale_for_search`], and all a
/// refresh can repair.
fn behind_build(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    among: impl IntoIterator<Item = SourceId>,
) -> Result<Vec<(Stale, Vec<Behind>)>> {
    let mut kept = Vec::new();
    for s in stale_among(repo, revisions, among)? {
        match behind(repo, revisions, &s)? {
            // Nothing the build declares is missing: the rows are the build's.
            Some(b) if b.is_empty() => {}
            behind => kept.push((s, behind.unwrap_or_default())),
        }
    }
    Ok(kept)
}

/// What a source's files declare that the index does not hold and no build
/// has compiled: the third way to fall behind, and the one a revision cannot
/// show.
///
/// A project's revision is its build, and the build moves only when somebody
/// builds it. Agents that build in a git worktree and merge into the main
/// checkout move its files and never its build, so the index was the build's
/// to the byte, four days and over a thousand files behind the source, and
/// `dt status` called it current. So the files are compared too: each one
/// saved after its module was last compiled is read, and the names it
/// declares are looked for among the rows of that module. A file only touched
/// -- a checkout, a merge that changed nothing in it -- declares what the
/// index has and costs a read; a name the index does not hold, or holds in
/// another module, is what makes the source behind.
///
/// Only modules the root imports count, by the files' own `import` lines, for
/// the reason [`Revisions::imported`] gives. `None` when nothing is missing,
/// when the source was never indexed -- then everything is missing, and
/// that is another message -- or when anything here cannot be read: a
/// warning that cries wolf on a source nobody can read is a warning nobody
/// reads.
pub fn unbuilt(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    id: &SourceId,
) -> Result<Option<(Stale, Vec<Behind>)>> {
    let Some(ahead) = revisions.unbuilt(id) else { return Ok(None) };
    if ahead.modules.is_empty() || repo.provenance(id)?.is_none() {
        return Ok(None);
    }
    // Read only once something is missing, as in `behind`: a file the root
    // does not import may declare anything, and no refresh would change that.
    let mut imported = None;
    let mut out = Vec::new();
    for (module, decls) in &ahead.modules {
        if decls.is_empty() {
            continue;
        }
        let Some(rows) = repo.located_in(id, module)? else { return Ok(None) };
        let missing: BTreeMap<DeclName, Located> = decls
            .iter()
            .filter(|(name, _)| !rows.contains_key(*name))
            .map(|(name, at)| (name.clone(), at.clone()))
            .collect();
        if missing.is_empty() {
            continue;
        }
        let Some(imported) = imported.get_or_insert_with(|| revisions.imported_as_written(id))
        else {
            return Ok(None);
        };
        if imported.contains(module) {
            out.push(Behind { module: module.clone(), decls: missing });
        }
    }
    let Some(Some(imported)) = imported.filter(|_| !out.is_empty()) else { return Ok(None) };
    let files = ahead.modules.keys().filter(|m| imported.contains(*m)).count();
    let why = Why::Unbuilt { files, project: ahead.project };
    Ok(Some((Stale { id: id.clone(), why }, out)))
}

/// The sources a miss may read again before it answers: the local ones in the
/// query's reach that a build has left behind.
///
/// Local only, and that is the whole point. A local source is rebuilt on
/// almost every edit and costs seconds to read again, so reading it is a
/// repair. A pinned dependency is rebuilt when somebody bumps it and costs
/// minutes, so reading it is a surprise -- and a Mathlib dump nobody asked
/// for is not an answer to a search.
pub fn refreshable(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    sources: &Sources,
    query: &Query,
) -> Result<Vec<SourceId>> {
    let among: Vec<SourceId> = sources
        .iter()
        .filter(|s| s.kind == SourceKind::Local)
        .filter(|s| query.source.as_ref().is_none_or(|asked| *asked == s.id))
        .map(|s| s.id.clone())
        .collect();
    // Not the files no build has compiled: reading the build again reads
    // what is already indexed.
    let stale = behind_build(repo, revisions, among)?;
    Ok(stale.into_iter().map(|(s, _)| s.id).collect())
}

/// A module the build has compiled since the index was written, and the
/// declarations in it the index does not hold as the build has them -- or,
/// for [`Why::Unbuilt`], a module saved since it was compiled, and the names
/// its file declares that the index does not hold there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Behind {
    pub module: ModuleName,
    /// Name → where the build puts it and how the source spells it, for the
    /// declarations that are new, moved or restated. From the `.ilean` or the
    /// file, so there is no type and no kind: this is what is known without a
    /// dump.
    pub decls: BTreeMap<DeclName, Located>,
}

/// What a source that moved has rebuilt and the index does not hold, or `None`
/// when that cannot be read -- which is every reason to rebuild an index that
/// the modules cannot show.
fn behind(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    s: &Stale,
) -> Result<Option<Vec<Behind>>> {
    if !matches!(s.why, Why::Moved { .. }) {
        return Ok(None);
    }
    let Some(was) = repo.provenance(&s.id)? else { return Ok(None) };
    let Some(declared) = revisions.declared_since(&s.id, was.indexed_at) else {
        return Ok(None);
    };
    // A build that moved and compiled nothing since has changed in a way the
    // modules cannot show -- a file deleted, or compiled while it was dumped.
    if declared.is_empty() {
        return Ok(None);
    }
    // The imports are read only when a module differs: a module the root does
    // not import differs from an index that never held it, and no refresh
    // would change that.
    let mut imported = None;
    let mut out = Vec::new();
    for (module, decls) in declared {
        let Some(rows) = repo.located_in(&s.id, &module)? else { return Ok(None) };
        let missing: BTreeMap<DeclName, Located> = decls
            .into_iter()
            .filter(|(name, built)| {
                built.span.is_none() || built.statement.is_none() || rows.get(name) != Some(built)
            })
            .collect();
        if missing.is_empty() {
            continue;
        }
        let Some(imported) = imported.get_or_insert_with(|| revisions.imported(&s.id)) else {
            return Ok(None);
        };
        if !imported.contains(&module) {
            continue;
        }
        out.push(Behind { module, decls: missing });
    }
    Ok(Some(out))
}

/// The declarations a rebuilt module has and the index does not, as far as the
/// query the search just missed can be asked of them.
///
/// Only a name and free text can be: an `.ilean` gives the name, the lines and
/// the statement as the source spells it, and no elaborated type at all, so a
/// shape or a `--uses` condition has nothing to match. A query carrying one is
/// not answered from here rather than answered loosely.
///
/// A module alone can: `--in Transformer.SaddleAvoidance` asks for what is
/// declared there, and when no row is, what the files declare is the answer.
/// A name the build and the file both declare is listed once, as the build
/// has it.
pub fn declared_matching(stale: &[(Stale, Vec<Behind>)], q: &Query) -> Vec<Declaration> {
    let asked = q.name_asked();
    if !q.shape.is_empty()
        || !q.uses.is_empty()
        || (asked.is_none() && q.text.is_empty() && q.module.is_none())
    {
        return Vec::new();
    }
    let mut out: Vec<Declaration> = Vec::new();
    for (s, behind) in stale {
        if q.source.as_ref().is_some_and(|id| id != &s.id) {
            continue;
        }
        for b in behind {
            if !q.module.as_ref().is_none_or(|m| b.module.is_under(m)) {
                continue;
            }
            for (name, at) in &b.decls {
                let named = asked.as_ref().is_none_or(|n| n.is_in(name.as_str()));
                let statement = at.statement.clone().unwrap_or_default();
                let spelled = q.text.iter().all(|t| {
                    statement.to_lowercase().contains(&t.to_lowercase())
                        || name.as_str().to_lowercase().contains(&t.to_lowercase())
                });
                let listed = out.iter().any(|d| d.source == s.id && &d.name == name);
                if named && spelled && !listed {
                    out.push(Declaration {
                        source: s.id.clone(),
                        module: b.module.clone(),
                        name: name.clone(),
                        line: at.span.map(|s| s.start),
                        statement: at.statement.clone(),
                        why: s.why.clone(),
                    });
                }
            }
        }
    }
    out
}

/// A declaration the build or the files have and the index does not. See
/// [`declared_matching`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declaration {
    pub source: SourceId,
    pub module: ModuleName,
    pub name: DeclName,
    /// The line it starts on, as the build or the file has it.
    pub line: Option<u32>,
    /// How the source spells it, when its file could be read.
    pub statement: Option<String>,
    /// Why the index does not hold it: [`Why::Moved`] for a declaration the
    /// build compiled since, [`Why::Unbuilt`] for one only the file has.
    pub why: Why,
}

impl Declaration {
    /// Whether a build has compiled it, so that `dt refresh` alone brings it
    /// into the index.
    pub fn compiled(&self) -> bool {
        !matches!(self.why, Why::Unbuilt { .. })
    }
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
        if !untouched && behind(repo, revisions, &s)?.is_none_or(|b| !b.is_empty()) {
            kept.push(s);
        }
    }
    Ok(kept)
}

/// The rows a command printed whose files now declare them in another module,
/// one no build has compiled since: what [`stale_for_rows`] cannot see, since
/// the module a row names may be untouched and still not where it is.
///
/// `Transformer.Perspective.IsStrictSaddleTorusEnergy` was printed from
/// `Transformer.Perspective.StrictSaddle` for days after a commit moved it to
/// `CircleCritical`: a real row that looked complete, and the only
/// `IsStrictSaddle` the search showed. A row whose module merely changed is
/// still the row, so only a name declared somewhere else counts.
pub fn moved_in_files(
    repo: &dyn DeclRepo,
    revisions: &dyn Revisions,
    rows: &BTreeMap<SourceId, BTreeMap<DeclName, ModuleName>>,
) -> Result<Vec<Relocated>> {
    let mut out = Vec::new();
    for (id, shown) in rows {
        let Some((stale, behind)) = unbuilt(repo, revisions, id)? else { continue };
        let mut moved = Vec::new();
        for b in &behind {
            for (name, at) in &b.decls {
                if shown.get(name).is_some_and(|m| *m != b.module) {
                    moved.push(Declaration {
                        source: id.clone(),
                        module: b.module.clone(),
                        name: name.clone(),
                        line: at.span.map(|s| s.start),
                        statement: at.statement.clone(),
                        why: stale.why.clone(),
                    });
                }
            }
        }
        if !moved.is_empty() {
            out.push(Relocated { stale, behind, moved });
        }
    }
    Ok(out)
}

/// A source whose files declare a printed row's name in another module now.
/// See [`moved_in_files`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Relocated {
    pub stale: Stale,
    /// All its files declare that the index does not hold, as [`unbuilt`]
    /// gives it: what the line about the source counts.
    pub behind: Vec<Behind>,
    /// The printed rows' names, where the files declare them now.
    pub moved: Vec<Declaration>,
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
            let ahead = unbuilt(self.repo, self.revisions, &s.id)?.and_then(|(s, behind)| {
                let Why::Unbuilt { files, project } = s.why else { return None };
                Some(Ahead { files, declaring: behind.len(), project })
            });
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
                ahead,
            });
        }
        Ok(Report {
            sources: out,
            unindexed: self.build.unindexed(),
            toolchain: self.build.toolchain(),
        })
    }
}
