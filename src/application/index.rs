//! Building the index: the dump for compiled sources, the text scan for the
//! rest, then whatever the sink does with the rows.

use crate::application::ports::{DeclRepo, DeclSink, DumpSpec, Elaborator, SourceFiles};
use crate::domain::decl::{Decl, DeclKind, Shape};
use crate::domain::lean_text;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::source::SourceMeta;
use crate::error::Result;
use std::path::PathBuf;

/// What one source contributed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceReport {
    pub source: String,
    pub decls: usize,
    pub elaborated: bool,
    /// Where the raw rows went, for a compiled source.
    pub jsonl: Option<PathBuf>,
}

/// Turn a text corpus into rows. Never runs Lean: the `.lean` files are read as
/// text, and every row carries `elaborated: false`.
///
/// `known` decides which scanned identifiers count as dependencies. Passing the
/// already-indexed corpus removes the bound variables and the notation that
/// would otherwise fill every dependency list with noise.
/// A text corpus as the scanner read it.
pub struct Scanned {
    pub decls: Vec<Decl>,
    /// Declarations the source gives no name of its own. See
    /// [`lean_text::Scan::anonymous`].
    pub anonymous: usize,
}

pub fn scan_source(
    meta: &SourceMeta,
    files: &dyn SourceFiles,
    known: Option<&dyn DeclRepo>,
) -> Result<Scanned> {
    let mut out = Vec::new();
    let mut anonymous = 0usize;
    for (module, path) in files.list_modules(&meta.id)? {
        let text = match std::fs::read_to_string(&path) {
            Ok(t) => t,
            // A corpus of 30 000 files will contain something unreadable; one
            // bad file must not lose the other 29 999.
            Err(_) => continue,
        };
        let imported = lean_text::imports(&text);
        let scan = lean_text::scan(&text);
        anonymous += scan.anonymous;
        for s in scan.decls {
            out.push(to_decl(meta, &module, s, &imported, known)?);
        }
    }
    Ok(Scanned { decls: out, anonymous })
}

fn to_decl(
    meta: &SourceMeta,
    module: &ModuleName,
    s: lean_text::Scanned,
    imported: &[ModuleName],
    known: Option<&dyn DeclRepo>,
) -> Result<Decl> {
    // Dependencies for a text source can only be approximated. Identifiers that
    // name something the index knows are kept; the rest are bound variables,
    // notation, or tactics.
    let mut deps: Vec<DeclName> = Vec::new();
    for ident in &s.idents {
        let real = match known {
            Some(repo) => repo.contains(ident)?,
            None => false,
        };
        if real && ident != &s.name {
            deps.push(ident.clone());
        }
    }
    let _ = imported;
    Ok(Decl {
        name: s.name,
        source: meta.id.clone(),
        module: module.clone(),
        kind: DeclKind::parse(&s.kind),
        ty: s.statement,
        // No elaborator, so no conclusion head symbol. Leaving this empty is
        // what keeps shape search from silently returning text rows.
        shape: Shape::default(),
        consts: s.idents,
        deps,
        doc: s.doc,
        has_sorry: s.has_sorry,
        span: Some(crate::domain::decl::Span::new(s.line_start, s.line_end)),
        elaborated: false,
    })
}

/// Run the Lean dump for a compiled source.
pub fn dump_source(
    meta: &SourceMeta,
    root: &str,
    modules: &[String],
    out: PathBuf,
    with_deps: bool,
    lean: &dyn Elaborator,
) -> Result<PathBuf> {
    lean.dump(&DumpSpec {
        source: meta.id.clone(),
        root: root.to_string(),
        modules: modules.to_vec(),
        out,
        with_deps,
    })
}

/// Feed rows into the index in batches.
///
/// The batch is the transaction, not the residency: the caller already holds
/// every row. One transaction per row is an fsync per row, and one transaction
/// for half a million rows is a journal the size of the index.
pub fn load(sink: &mut dyn DeclSink, decls: &[Decl]) -> Result<usize> {
    const BATCH: usize = 8192;
    for chunk in decls.chunks(BATCH) {
        sink.put(chunk)?;
    }
    Ok(decls.len())
}
