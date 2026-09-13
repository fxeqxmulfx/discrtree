//! `dt deps <name>` — what a proof rests on.
//!
//! Depth 1-2 is the readable regime. `--depth all` prints a count first and the
//! list only when asked again, because the full closure of a two-line lemma
//! about `exp` is 5154 declarations.

use crate::application::ports::{DeclRepo, Workspace};
use crate::domain::closure::{self, ClosureStats, DeclSource};
use crate::domain::decl::Decl;
use crate::domain::name::DeclName;
use crate::error::{Result, bail};

/// A repository read through the closure walk's eyes. The walk is pure; this
/// adapter is where it meets the index.
pub struct RepoSource<'a> {
    pub repo: &'a dyn DeclRepo,
    pub workspace: &'a Workspace,
}

impl DeclSource for RepoSource<'_> {
    fn get(&self, name: &DeclName) -> Option<Decl> {
        self.repo.get(name).ok().flatten()
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

pub struct Deps<'a> {
    pub repo: &'a dyn DeclRepo,
    pub workspace: &'a Workspace,
}

impl Deps<'_> {
    pub fn run(&self, name: &DeclName, depth: Option<usize>) -> Result<DepsResult> {
        let Some(root) = self.repo.get(name)? else { bail!("{name} is not in the index") };
        // A text row's dependencies were guessed from imports and identifiers.
        // Saying so is not optional: a list that mixed the two silently would
        // be worse than no list.
        let approximate = !root.elaborated;
        let src = RepoSource { repo: self.repo, workspace: self.workspace };
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
