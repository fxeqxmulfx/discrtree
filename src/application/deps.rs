//! `dt deps <name>` — what a proof rests on.
//!
//! Depth 1-2 is the readable regime. `--depth all` prints a count first and the
//! list only when asked again, because the full closure of a two-line lemma
//! about `exp` is 5154 declarations.

use crate::application::ports::{Build, DeclRepo, Workspace};
use crate::domain::closure::{self, ClosureStats, DeclSource};
use crate::domain::decl::Decl;
use crate::domain::name::DeclName;
use crate::domain::source::SourceId;
use crate::error::{Result, bail};
use std::collections::BTreeSet;

/// A repository read through the closure walk's eyes. The walk is pure; this
/// adapter is where it meets the index.
pub struct RepoSource<'a> {
    pub repo: &'a dyn DeclRepo,
    pub workspace: &'a Workspace,
    /// The row the walk starts from, when `--source` chose one other than the
    /// row the name means by default. Only the root: a dependency is the
    /// constant the proof names, and the default row is still the one it
    /// means.
    pub root: Option<Decl>,
}

impl DeclSource for RepoSource<'_> {
    fn get(&self, name: &DeclName) -> Option<Decl> {
        match &self.root {
            Some(root) if &root.name == name => Some(root.clone()),
            _ => self.repo.get(name).ok().flatten(),
        }
    }
    fn is_importable(&self, d: &Decl) -> bool {
        self.workspace.sources.importable(&d.source)
    }
}

pub enum DepsResult {
    /// One list per level, nearest first.
    Levels { root: Decl, levels: Vec<Vec<Decl>>, approximate: bool },
    /// `--depth all`: the size of the closure, not its contents.
    Summary { root: Decl, stats: ClosureStats, approximate: bool },
}

/// The row `name` has in `only_in`, or the one it means by default.
///
/// A name in other sources and not in `only_in` is an error that names them,
/// which is the correction; a name in none is `None`, for the caller to
/// explain.
pub fn row_in(
    repo: &dyn DeclRepo,
    name: &DeclName,
    only_in: Option<&SourceId>,
) -> Result<Option<Decl>> {
    let rows = repo.named(name)?;
    let has: BTreeSet<String> = rows.iter().map(|d| format!("`{}`", d.source)).collect();
    match rows.into_iter().find(|d| only_in.is_none_or(|s| &d.source == s)) {
        Some(d) => Ok(Some(d)),
        None => match only_in {
            Some(s) if !has.is_empty() => {
                bail!("{name} is in {}, not in `{s}`", Vec::from_iter(has).join(", "))
            }
            _ => Ok(None),
        },
    }
}

pub struct Deps<'a> {
    pub repo: &'a dyn DeclRepo,
    pub workspace: &'a Workspace,
    /// Consulted only when the name is missing. `dt deps` is where a reader
    /// arrives holding a fully qualified name they read somewhere, which is
    /// exactly the case a namespace can be read off.
    pub build: &'a dyn Build,
    /// The source to take the root from. See [`RepoSource::root`].
    pub only_in: Option<&'a SourceId>,
}

impl Deps<'_> {
    pub fn run(&self, name: &DeclName, depth: Option<usize>) -> Result<DepsResult> {
        let Some(root) = row_in(self.repo, name, self.only_in)? else {
            if let Some(missing) = self.build.declaring(name.as_str()) {
                bail!("{}", missing.about(name))
            }
            bail!("{name} is not in the index")
        };
        // A text row's dependencies were guessed from imports and identifiers.
        // Saying so is not optional: a list that mixed the two silently would
        // be worse than no list.
        let approximate = !root.elaborated;
        let src =
            RepoSource { repo: self.repo, workspace: self.workspace, root: Some(root.clone()) };
        Ok(match depth {
            Some(d) => {
                DepsResult::Levels { levels: closure::levels(name, &src, d), root, approximate }
            }
            None => {
                DepsResult::Summary { stats: closure::closure_size(name, &src), root, approximate }
            }
        })
    }
}
