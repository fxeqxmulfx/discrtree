//! Turning use-case results into what appears in the terminal.
//!
//! Every result line says whether the row was elaborated. A search that
//! silently mixed compiled and text corpora would be worse than no search, so
//! the marker is not optional and not a verbosity setting.

use crate::application::add::AddReport;
use crate::application::deps::DepsResult;
use crate::application::find::Duplicate;
use crate::application::show::Shown;
use crate::application::status::SourceStatus;
use crate::domain::decl::Decl;

/// The marker every text row carries.
pub fn mark(d: &Decl) -> &'static str {
    if d.elaborated { "" } else { "  [text]" }
}

fn sorry_mark(d: &Decl) -> &'static str {
    if d.has_sorry { "  [sorry]" } else { "" }
}

pub fn find(hits: &[Decl], long: bool) -> String {
    if hits.is_empty() {
        return "no match\n".into();
    }
    let mut out = String::new();
    for d in hits {
        out.push_str(&format!(
            "{}{}{}\n  {}  {}\n",
            d.name,
            mark(d),
            sorry_mark(d),
            d.kind,
            d.module
        ));
        let ty = if long { d.ty.as_str() } else { first_line(&d.ty, 100) };
        if !ty.is_empty() {
            out.push_str(&format!("  {ty}\n"));
        }
        if let Some(s) = d.summary() {
            out.push_str(&format!("  -- {}\n", first_line(s, 100)));
        }
        out.push('\n');
    }
    out.push_str(&format!("{} result(s)\n", hits.len()));
    out
}

pub fn show(s: &Shown, import_only: bool) -> String {
    let mut out = String::new();
    match &s.import {
        Some(i) => out.push_str(&format!("{i}\n")),
        None => out.push_str(&format!(
            "-- source `{}` is not importable; `dt add {}` copies it instead\n",
            s.decl.source, s.decl.name
        )),
    }
    if import_only {
        return out;
    }
    out.push('\n');
    out.push_str(&format!(
        "{}{}{}\n  {}  {}",
        s.decl.name,
        mark(&s.decl),
        sorry_mark(&s.decl),
        s.decl.kind,
        s.decl.module
    ));
    if let Some(span) = s.decl.span {
        out.push_str(&format!(":{}-{}", span.start, span.end));
    }
    out.push_str("\n\n");
    match (&s.source_text, &s.note) {
        (Some(t), _) => {
            out.push_str(t);
            out.push('\n');
        }
        (None, Some(n)) => {
            out.push_str(&format!("-- source not available: {n}\n-- type: {}\n", s.decl.ty))
        }
        (None, None) => out.push_str(&format!("-- type: {}\n", s.decl.ty)),
    }
    out
}

pub fn deps(r: &DepsResult) -> String {
    let mut out = String::new();
    match r {
        DepsResult::Levels { root, levels, approximate } => {
            out.push_str(&format!("{}{}\n", root.name, mark(root)));
            if *approximate {
                out.push_str(
                    "-- approximate: this source is indexed as text, so dependencies are guessed\n\
                     -- from imports and identifiers, not read off a proof term\n",
                );
            }
            if levels.is_empty() {
                out.push_str("\nno dependencies recorded\n");
                return out;
            }
            for (i, level) in levels.iter().enumerate() {
                out.push_str(&format!("\ndepth {}  ({} declarations)\n", i + 1, level.len()));
                for d in level {
                    out.push_str(&format!("  {:<52} {}{}\n", d.name.as_str(), d.source, mark(d)));
                }
            }
        }
        DepsResult::Summary { root, stats, approximate } => {
            out.push_str(&format!("{}{}\n\n", root.name, mark(root)));
            if *approximate {
                out.push_str("-- approximate: dependencies guessed from text\n\n");
            }
            out.push_str(&format!(
                "{} declarations in the transitive closure, {} of them theorems\n",
                stats.total, stats.theorems
            ));
            for (source, n) in &stats.by_source {
                out.push_str(&format!("  {source:<16} {n}\n"));
            }
            out.push_str("\nRe-run with --depth 1 or --depth 2 for the readable part.\n");
        }
    }
    out
}

pub fn add(r: &AddReport, written: bool) -> String {
    let mut out = String::new();
    if r.approximate {
        out.push_str(
            "-- approximate: part of this tree comes from a source indexed as text,\n\
             -- so its dependencies are guessed rather than read off a proof term\n\n",
        );
    }
    if !r.frontier.imports.is_empty() {
        out.push_str("imports\n");
        for m in &r.frontier.imports {
            out.push_str(&format!("  {}\n", m.import_line()));
        }
        out.push('\n');
    }
    if r.is_import_only() {
        out.push_str(
            "Nothing to copy: every dependency is reachable by an import.\n\
             That is the whole answer, not a degenerate one.\n",
        );
        return out;
    }
    out.push_str(&format!(
        "to materialize: {} declaration(s) in {} file(s), {} lines, tree depth {}\n\n",
        r.plan.total_decls(),
        r.plan.files.len(),
        r.plan.total_lines(),
        r.frontier.depth
    ));
    for (source, n) in &r.plan.by_source {
        out.push_str(&format!("  {source:<16} {n}\n"));
    }
    out.push('\n');
    for f in &r.plan.files {
        out.push_str(&format!(
            "  {:<58} {} decl(s), {} lines\n",
            f.path.display(),
            f.decls.len(),
            f.lines()
        ));
    }
    if !r.frontier.missing.is_empty() {
        out.push_str(&format!(
            "\n{} dependency(ies) are not in the index, so this tree is incomplete:\n",
            r.frontier.missing.len()
        ));
        for m in r.frontier.missing.iter().take(10) {
            out.push_str(&format!("  {m}\n"));
        }
    }
    if written {
        out.push_str(&format!(
            "\nwritten: {} file(s); registered {} module(s) in the aggregator\n",
            r.written.len(),
            r.registered.len()
        ));
    } else {
        out.push_str("\nDry run. Nothing was written; re-run with --write.\n");
    }
    out
}

pub fn status(rows: &[SourceStatus], db: &std::path::Path) -> String {
    let mut out = format!("index: {}\n\n", db.display());
    out.push_str(&format!(
        "{:<14} {:<7} {:<12} {:<12} {:>10}\n",
        "source", "kind", "elaborated", "importable", "declarations"
    ));
    for r in rows {
        out.push_str(&format!(
            "{:<14} {:<7} {:<12} {:<12} {:>10}\n",
            r.name,
            r.kind.as_str(),
            r.elaborated,
            r.importable,
            r.decls
        ));
    }
    let total: usize = rows.iter().map(|r| r.decls).sum();
    out.push_str(&format!("\n{total} declarations indexed\n"));
    if rows.iter().any(|r| r.decls == 0) {
        out.push_str("\nA source with no declarations has not been dumped or scanned yet.\n");
    }
    out
}

pub fn dup(dups: &[Duplicate]) -> String {
    if dups.is_empty() {
        return "nothing here looks like an upstream declaration\n".into();
    }
    let mut out = String::new();
    for d in dups {
        out.push_str(&format!("{}\n  {}\n", d.local.name, first_line(&d.local.ty, 100)));
        for c in &d.candidates {
            out.push_str(&format!(
                "  {:>3}%  {}{}\n         {}\n",
                (c.similarity * 100.0).round() as u32,
                c.decl.name,
                mark(&c.decl),
                c.decl.module
            ));
        }
        out.push('\n');
    }
    out.push_str(&format!("{} declaration(s) with upstream candidates\n", dups.len()));
    out
}

/// The first line, cut to `width` on a character boundary.
fn first_line(s: &str, width: usize) -> &str {
    let line = s.lines().next().unwrap_or("");
    match line.char_indices().nth(width) {
        Some((i, _)) => &line[..i],
        None => line,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::decl::Span;

    fn decl(elaborated: bool) -> Decl {
        let mut d =
            Decl::stub("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Complex.Exponential");
        d.ty = "Real.exp x ≤ Real.exp y ↔ x ≤ y".into();
        d.span = Some(Span::new(316, 318));
        d.elaborated = elaborated;
        d
    }

    #[test]
    fn every_text_row_is_marked_as_such() {
        let rendered = find(&[decl(false)], false);
        assert!(rendered.contains("[text]"), "got: {rendered}");
        assert!(!find(&[decl(true)], false).contains("[text]"));
    }

    #[test]
    fn show_leads_with_the_import_that_provides_it() {
        let s = Shown {
            decl: decl(true),
            import: Some("import Mathlib.Analysis.Complex.Exponential".into()),
            source_text: Some("theorem exp_le_exp : True := trivial".into()),
            note: None,
        };
        let out = show(&s, false);
        assert!(out.starts_with("import Mathlib.Analysis.Complex.Exponential\n"));
        assert!(out.contains("316-318"));
        assert!(out.contains("theorem exp_le_exp"));
    }

    #[test]
    fn show_says_so_when_a_source_cannot_be_imported() {
        let s = Shown { decl: decl(false), import: None, source_text: None, note: None };
        assert!(show(&s, true).contains("not importable"));
    }

    #[test]
    fn cutting_a_long_type_never_splits_a_character() {
        let wide = "≤".repeat(200);
        assert_eq!(first_line(&wide, 10).chars().count(), 10);
    }

    #[test]
    fn an_empty_result_says_so_rather_than_printing_nothing() {
        assert_eq!(find(&[], false), "no match\n");
    }
}
