//! `dt show <name>` — the declaration's source verbatim, plus the `import` line
//! that actually provides it.
//!
//! That import is the real value. `Real.exp_le_exp` lives in
//! `Mathlib.Analysis.Complex.Exponential`, not in the
//! `Mathlib.Analysis.SpecialFunctions.Exp` one would guess, which does not
//! contain it at all.

use crate::application::generated;
use crate::application::ports::{DeclRepo, Packages, SourceFiles, Workspace};
use crate::domain::decl::Decl;
use crate::domain::lean_text;
use crate::domain::name::DeclName;
use crate::error::{Result, bail};

#[derive(Debug, Clone)]
pub struct Shown {
    pub decl: Decl,
    /// The import line that provides it, or `None` for a source that cannot be
    /// imported.
    pub import: Option<String>,
    pub source: Source,
}

/// What the indexed line range turned out to hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// The declaration's own lines.
    Text(String),
    /// The range holds no declaration at all.
    ///
    /// Lean points a *generated* declaration at whatever syntax produced it:
    /// `Finset.sum_image` gets the range of the `to_additive` block above
    /// `theorem prod_image`, and a structure field gets the field line. Printing
    /// those lines as the declaration is worse than printing nothing, because
    /// they read like an answer and stop exactly where the useful part starts.
    /// 57 443 of Mathlib's 325 936 rows have a range inside another's.
    Generated {
        /// The declaration whose range contains this one, when there is one.
        /// That is the declaration that generated it, and the one whose source
        /// carries the proof.
        inside: Option<Box<Decl>>,
        /// The first non-blank line of the range, for when there is not — an
        /// `alias` produced by `to_dual` names its original there.
        head: String,
    },
    /// No lines at all: no range in the index, or the file is not on disk.
    Missing(String),
}

pub struct Show<'a> {
    pub repo: &'a dyn DeclRepo,
    pub files: &'a dyn SourceFiles,
    pub workspace: &'a Workspace,
    /// Consulted only when the name is missing, to tell a name the index does
    /// not have from a corpus the index never had.
    pub packages: &'a dyn Packages,
}

impl Show<'_> {
    pub fn run(&self, name: &DeclName) -> Result<Shown> {
        let Some(decl) = self.repo.get(name)? else {
            // `try --name` is good advice only when the name might be in the
            // index under a different spelling. When the namespace belongs to a
            // package nothing indexed, that search returns the same nothing, or
            // worse, a page of near-misses from Mathlib that read like an
            // answer. Say which corpus is missing instead.
            if let Some(p) = self.packages.providing(name.as_str()) {
                bail!(
                    "{name} is in the lake package `{}`, which is not a source of this index; \
                     add it to discrtree.toml and re-run `dt dump {}` and `dt index`",
                    p.name,
                    p.name
                )
            }
            bail!("{name} is not in the index; try `dt find --name {}`", name.base())
        };
        let import =
            self.workspace.sources.importable(&decl.source).then(|| decl.module.import_line());

        let source = self.source_of(&decl)?;
        Ok(Shown { decl, import, source })
    }

    fn source_of(&self, decl: &Decl) -> Result<Source> {
        let Some(span) = decl.span else {
            return Ok(Source::Missing("the index has no line range for this declaration".into()));
        };
        let text = match self.files.read_module(&decl.source, &decl.module) {
            Ok(t) => t,
            Err(e) => return Ok(Source::Missing(format!("{e}"))),
        };
        let lines = span.slice(&text).join("\n");
        if lean_text::declares_name(&lines, &decl.name) {
            return Ok(Source::Text(lines));
        }
        let inside = generated::generator(self.repo, decl, &text)?;
        // The lines declare something else, and nothing in the module contains
        // them: believe the file. Lean's naming is not a parser, and a name the
        // header spells in a way this does not recognise is still likelier than
        // a declaration with no source at all.
        if inside.is_none() && lean_text::declares(&lines) {
            return Ok(Source::Text(lines));
        }
        let head = lines.lines().map(str::trim).find(|l| !l.is_empty()).unwrap_or("").to_string();
        Ok(Source::Generated { inside: inside.map(Box::new), head })
    }
}
