//! `dt show <name>` — the declaration's source verbatim, plus the `import` line
//! that actually provides it.
//!
//! That import is the real value. `Real.exp_le_exp` lives in
//! `Mathlib.Analysis.Complex.Exponential`, not in the
//! `Mathlib.Analysis.SpecialFunctions.Exp` one would guess, which does not
//! contain it at all.

use crate::application::ports::{DeclRepo, SourceFiles, Workspace};
use crate::domain::decl::Decl;
use crate::domain::name::DeclName;
use crate::error::{Result, bail};

#[derive(Debug, Clone)]
pub struct Shown {
    pub decl: Decl,
    /// The import line that provides it, or `None` for a source that cannot be
    /// imported.
    pub import: Option<String>,
    /// The declaration's own lines. `None` when the file is not on disk or the
    /// index has no range for it.
    pub source_text: Option<String>,
    /// Why `source_text` is missing, when it is.
    pub note: Option<String>,
}

pub struct Show<'a> {
    pub repo: &'a dyn DeclRepo,
    pub files: &'a dyn SourceFiles,
    pub workspace: &'a Workspace,
}

impl Show<'_> {
    pub fn run(&self, name: &DeclName) -> Result<Shown> {
        let Some(decl) = self.repo.get(name)? else {
            bail!("{name} is not in the index; try `dt find --name {}`", name.base())
        };
        let import =
            self.workspace.sources.importable(&decl.source).then(|| decl.module.import_line());

        let (source_text, note) = match decl.span {
            None => (None, Some("the index has no line range for this declaration".into())),
            Some(span) => match self.files.read_module(&decl.source, &decl.module) {
                Ok(text) => (Some(span.slice(&text).join("\n")), None),
                Err(e) => (None, Some(format!("{e}"))),
            },
        };
        Ok(Shown { decl, import, source_text, note })
    }
}
