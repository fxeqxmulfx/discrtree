//! `dt status` — what is indexed, and whether it can be trusted.

use crate::application::ports::{DeclRepo, Workspace};
use crate::domain::source::SourceKind;
use crate::error::Result;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceStatus {
    pub name: String,
    pub kind: SourceKind,
    pub elaborated: bool,
    pub importable: bool,
    pub decls: usize,
    pub rev: Option<String>,
}

pub struct Status<'a> {
    pub repo: &'a dyn DeclRepo,
    pub workspace: &'a Workspace,
}

impl Status<'_> {
    pub fn run(&self) -> Result<Vec<SourceStatus>> {
        let counts = self.repo.counts()?;
        Ok(self
            .workspace
            .sources
            .iter()
            .map(|s| SourceStatus {
                name: s.id.to_string(),
                kind: s.kind,
                elaborated: s.elaborated,
                importable: s.importable,
                decls: counts.iter().find(|(id, _)| id == &s.id).map_or(0, |(_, n)| *n),
                rev: s.rev.clone(),
            })
            .collect())
    }
}
