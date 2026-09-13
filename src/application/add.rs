//! `dt add <name>` — materialize a declaration and its tree into the project.
//!
//! Dry run by default. Nothing is written without `--write`, because the depth
//! of the materialization set cannot be predicted from the name: for a Mathlib
//! target it is empty and the whole answer is one import line, and for a source
//! that cannot be imported an arbitrarily deep tree is the normal case, not an
//! edge case.

use crate::application::deps::RepoSource;
use crate::application::generated;
use crate::application::ports::{DeclRepo, ProjectWriter, SourceFiles, Workspace};
use crate::domain::closure::{self, Frontier};
use crate::domain::decl::Decl;
use crate::domain::lean_text;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::vendor::{self, VendorPlan};
use crate::error::{Result, bail};

pub struct AddReport {
    pub frontier: Frontier,
    pub plan: VendorPlan,
    /// Set when any node's dependencies were guessed from text. The report says
    /// so, and so does the header of anything written.
    pub approximate: bool,
    /// Files actually written. Empty on a dry run.
    pub written: Vec<std::path::PathBuf>,
    /// Modules registered in the aggregator. Empty on a dry run.
    pub registered: Vec<ModuleName>,
}

impl AddReport {
    /// For a Mathlib target the materialization set is empty and the answer is
    /// one import line — the correct outcome, not a degenerate one.
    pub fn is_import_only(&self) -> bool {
        self.plan.is_empty()
    }
}

pub struct Add<'a> {
    pub repo: &'a dyn DeclRepo,
    pub files: &'a dyn SourceFiles,
    pub workspace: &'a Workspace,
}

impl Add<'_> {
    /// Resolve the frontier and plan the write. Touches nothing.
    pub fn plan(&self, name: &DeclName) -> Result<AddReport> {
        if self.repo.get(name)?.is_none() {
            bail!("{name} is not in the index; try `dt find --name {}`", name.base())
        }
        let src = RepoSource { repo: self.repo, workspace: self.workspace };
        let frontier = closure::frontier(std::slice::from_ref(name), &src);

        // Only what is left after importable subtrees collapsed gets copied,
        // and a declaration already reachable by an import is never copied.
        let to_copy: Vec<Decl> = self
            .repo
            .get_many(&frontier.materialize)?
            .into_iter()
            .filter(|d| !self.workspace.sources.importable(&d.source))
            .collect();

        let imports: Vec<ModuleName> = frontier.imports.iter().cloned().collect();
        let plan = vendor::plan(
            &to_copy,
            &imports,
            &self.workspace.vendor_dir,
            &self.workspace.vendor_module,
            &|id| self.workspace.meta(id),
        );
        Ok(AddReport {
            approximate: frontier.approximate,
            frontier,
            plan,
            written: Vec::new(),
            registered: Vec::new(),
        })
    }

    /// Emit the plan. Files land in topological order with a provenance header,
    /// and the new modules are registered in the aggregator so they are built.
    pub fn write(
        &self,
        name: &DeclName,
        writer: &mut dyn ProjectWriter,
        force: bool,
    ) -> Result<AddReport> {
        let mut report = self.plan(name)?;
        for file in &report.plan.files {
            let text = self.render(file)?;
            writer.write_module(&file.path, &text, force)?;
            report.written.push(file.path.clone());
        }
        report.registered = writer.add_imports(&report.plan.imports)?;
        Ok(report)
    }

    /// A vendored module: provenance header, imports, then the declarations
    /// copied verbatim from upstream.
    fn render(&self, file: &crate::domain::vendor::VendorFile) -> Result<String> {
        let mut out = String::with_capacity(4096);
        out.push_str(&file.header);
        out.push_str("\n\n");
        for m in &file.imports {
            out.push_str(&m.import_line());
            out.push('\n');
        }
        if !file.imports.is_empty() {
            out.push('\n');
        }
        // A generated declaration resolves to the declaration that generated it,
        // and a `to_additive` pair in one file resolves to the same block twice.
        // Emitting it twice is not merely wasteful: the second copy redeclares
        // the first, and the vendored module does not compile.
        let mut seen = std::collections::BTreeSet::new();
        for decl in &file.decls {
            let (module, start, end, text) = self.text_of(decl)?;
            if !seen.insert((module, start, end)) {
                continue;
            }
            out.push_str(&text);
            if !text.ends_with('\n') {
                out.push('\n');
            }
            out.push('\n');
        }
        Ok(out)
    }

    /// The lines to copy for one declaration, and the range they came from.
    ///
    /// Not always the declaration's own range. Lean points a generated
    /// declaration at the syntax that produced it — `to_additive` at an
    /// attribute block, a structure's field at a line of the structure — and
    /// copying those lines vendors an attribute with no declaration under it.
    /// The declaration that encloses them is the one to copy: elaborating it
    /// produces this one again.
    fn text_of(&self, decl: &Decl) -> Result<(ModuleName, u32, u32, String)> {
        let Some(span) = decl.span else {
            bail!("{}: the index has no line range, so it cannot be copied", decl.name)
        };
        let text = self.files.read_module(&decl.source, &decl.module)?;
        let lines = span.slice(&text);
        if lines.is_empty() {
            bail!(
                "{}: lines {}-{} of {} are not there; re-run `dt index` after the source moved",
                decl.name,
                span.start,
                span.end,
                decl.module
            )
        }
        let joined = lines.join("\n");
        if lean_text::declares_name(&joined, &decl.name) {
            return Ok((decl.module.clone(), span.start, span.end, joined));
        }
        match generated::generator(self.repo, decl, &text)? {
            Some(up) => self.text_of(&up),
            None => Ok((decl.module.clone(), span.start, span.end, joined)),
        }
    }
}
