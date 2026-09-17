//! `dt show <name>` — the declaration's source verbatim, plus the `import` line
//! that actually provides it.
//!
//! That import is the real value. `Real.exp_le_exp` lives in
//! `Mathlib.Analysis.Complex.Exponential`, not in the
//! `Mathlib.Analysis.SpecialFunctions.Exp` one would guess, which does not
//! contain it at all.

use crate::application::deps::row_in;
use crate::application::generated;
use crate::application::ports::{Build, DeclRepo, SourceFiles, Workspace};
use crate::application::rdeps::SHOWN;
use crate::domain::decl::Decl;
use crate::domain::lean_text;
use crate::domain::name::DeclName;
use crate::domain::source::SourceId;
use crate::error::{Result, bail};

#[derive(Debug, Clone)]
pub struct Shown {
    pub decl: Decl,
    /// The import line that provides it, or `None` for a source that cannot be
    /// imported.
    pub import: Option<String>,
    pub source: Source,
    /// The name as it was asked for, when that was only the end of this one's:
    /// `countP_range'_add` for `Transformer.CRASP.countP_range'_add`.
    pub asked: Option<DeclName>,
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
        /// The first line of the range that is neither blank nor a comment,
        /// for when there is not — an `alias` produced by `to_dual` names its
        /// original there.
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
    pub build: &'a dyn Build,
    /// The source to take the row from. A name is nearly always in one, and
    /// without this a name a text corpus shares with a compiled source is
    /// shown from the compiled one.
    pub only_in: Option<&'a SourceId>,
}

impl Show<'_> {
    pub fn run(&self, name: &DeclName) -> Result<Shown> {
        if let Some(decl) = row_in(self.repo, name, self.only_in)? {
            return self.shown(decl, None);
        }
        let Some(decl) = self.ending(name)? else {
            // `try --name` is good advice only when the name might be in the
            // index under a different spelling. When the namespace belongs to a
            // package nothing indexed, that search returns the same nothing, or
            // worse, a page of near-misses from Mathlib that read like an
            // answer. Say which corpus is missing instead.
            if let Some(missing) = self.build.declaring(name.as_str()) {
                bail!("{}", missing.about(name))
            }
            bail!("{name} is not in the index; try `dt find --name {}`", name.base())
        };
        self.shown(decl, Some(name.clone()))
    }

    fn shown(&self, decl: Decl, asked: Option<DeclName>) -> Result<Shown> {
        let import =
            self.workspace.sources.importable(&decl.source).then(|| decl.module.import_line());
        let source = self.source_of(&decl)?;
        Ok(Shown { decl, import, source, asked })
    }

    /// The one declaration whose name ends in `name`. Inside `namespace
    /// Transformer.CRASP` a theorem is written without its namespace, and that
    /// is the spelling a reader copies out of the file. When several end in
    /// it, the project's own is the one meant if it is the only one; otherwise
    /// the reader has to say which.
    fn ending(&self, name: &DeclName) -> Result<Option<Decl>> {
        let field = match name.is_field() {
            true => name.clone(),
            false => DeclName::new(format!(".{name}")),
        };
        let mut named = self.repo.ending_in(&field)?;
        if let Some(s) = self.only_in {
            let mut kept = Vec::new();
            for n in named {
                if self.repo.named(&n)?.iter().any(|d| &d.source == s) {
                    kept.push(n);
                }
            }
            named = kept;
        }
        let own = format!("{}.", self.workspace.namespace);
        let mine: Vec<&DeclName> = named.iter().filter(|n| n.as_str().starts_with(&own)).collect();
        let meant = match (named.len(), mine.len()) {
            (0, _) => return Ok(None),
            (1, _) => named[0].clone(),
            (_, 1) => mine[0].clone(),
            (n, _) => {
                named.sort_by_key(|n| !n.as_str().starts_with(&own));
                let shown: Vec<&str> = named.iter().take(SHOWN).map(DeclName::as_str).collect();
                let more = match n.saturating_sub(SHOWN) {
                    0 => String::new(),
                    m => format!(", and {m} more"),
                };
                bail!("{n} declarations end in {name}; name one: {}{more}", shown.join(", "))
            }
        };
        row_in(self.repo, &meant, self.only_in)
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
        let head = lean_text::first_code_line(&lines).to_string();
        Ok(Source::Generated { inside: inside.map(Box::new), head })
    }
}
