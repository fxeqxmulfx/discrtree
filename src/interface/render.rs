//! Turning use-case results into what appears in the terminal.
//!
//! Every result line says whether the row was elaborated. A search that
//! silently mixed compiled and text corpora would be worse than no search, so
//! the marker is not optional and not a verbosity setting.

use crate::application::add::AddReport;
use crate::application::deps::DepsResult;
use crate::application::find::{Duplicate, Empty, Hits};
use crate::application::show::Shown;
use crate::application::status::SourceStatus;
use crate::domain::decl::Decl;
use std::collections::BTreeMap;

/// The marker every text row carries.
pub fn mark(d: &Decl) -> &'static str {
    if d.elaborated { "" } else { "  [text]" }
}

fn sorry_mark(d: &Decl) -> &'static str {
    if d.has_sorry { "  [sorry]" } else { "" }
}

/// A hit is two lines: what it is called, followed by what it says.
///
/// Nothing here is padded or separated by blank lines. This output is read far
/// more often by a program than by a person, and alignment whitespace is paid
/// for on every read while carrying no information. The docstring is the other
/// half of that bargain: it is a quarter of the output and almost never the
/// reason a search succeeds, so it waits for `--long`.
pub fn find(hits: &Hits, long: bool) -> String {
    if hits.rows.is_empty() {
        // Which repair to make is the whole question, and it is already known
        // here. Saying only "no match" makes the caller guess between editing a
        // condition and dropping one, and a wrong guess costs another search.
        return match &hits.empty {
            Some(Empty::Barren(c)) if c.len() == 1 => {
                format!("no match: {} matches nothing on its own\n", c[0])
            }
            Some(Empty::Barren(c)) => {
                format!("no match: {} match nothing on their own\n", c.join(", "))
            }
            Some(Empty::Combination) => {
                "no match: every condition matches on its own; drop one\n".into()
            }
            _ => "no match\n".into(),
        };
    }
    let mut out = String::new();
    for d in &hits.rows {
        out.push_str(&format!(
            "{}{}{}  {}  {}\n",
            d.name,
            mark(d),
            sorry_mark(d),
            d.kind,
            d.module
        ));
        let ty = if long { d.ty.as_str().into() } else { first_line(&d.ty, 100) };
        if !ty.is_empty() {
            out.push_str(&format!("  {ty}\n"));
        }
        if long {
            if let Some(s) = d.summary() {
                out.push_str(&format!("  -- {}\n", first_line(s, 200)));
            }
        }
    }
    // Saying only the count leaves the reader unable to tell a complete answer
    // from a truncated one without running the search again.
    if hits.truncated {
        out.push_str(&format!("{} shown, more match; refine or --limit\n", hits.rows.len()));
    } else {
        out.push_str(&format!("{} result(s)\n", hits.rows.len()));
    }
    out
}

/// Several declarations in one answer.
///
/// `--import-only` deduplicates: asking for four lemmas from one module must
/// not produce the same import line four times, and the caller pasting the
/// result should not have to notice.
pub fn show_all(shown: &[Shown], import_only: bool) -> String {
    if import_only {
        let mut seen: Vec<String> = Vec::new();
        let mut out = String::new();
        for s in shown {
            let line = match &s.import {
                Some(i) => i.clone(),
                None => format!(
                    "-- source `{}` is not importable; `dt add {}` copies it instead",
                    s.decl.source, s.decl.name
                ),
            };
            if !seen.contains(&line) {
                out.push_str(&line);
                out.push('\n');
                seen.push(line);
            }
        }
        return out;
    }
    shown.iter().map(|s| show(s, false)).collect::<Vec<_>>().join("\n")
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
                out.push_str(&format!("depth {} ({})\n", i + 1, level.len()));
                out.push_str(&by_source(level));
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
                out.push_str(&format!("  {source} {n}\n"));
            }
            out.push_str("\nRe-run with --depth 1 or --depth 2 for the readable part.\n");
        }
    }
    out
}

/// A level of the dependency tree, grouped by the source each name came from.
///
/// A dependency list is a set of names, not a table: one line per name with the
/// source repeated beside it spends most of its width restating `mathlib`. The
/// source is the thing that repeats, so it is said once and the names follow.
fn by_source(level: &[Decl]) -> String {
    let mut groups: BTreeMap<(&str, &str), Vec<&str>> = BTreeMap::new();
    for d in level {
        groups.entry((d.source.as_str(), mark(d))).or_default().push(d.name.as_str());
    }
    let mut out = String::new();
    for ((source, text), names) in groups {
        out.push_str(&wrapped(&format!("  {source}{text}:"), &names));
    }
    out
}

/// `head` followed by `items`, broken at `WIDTH` so a long level stays legible
/// without one line per item.
fn wrapped(head: &str, items: &[&str]) -> String {
    const WIDTH: usize = 96;
    let mut out = String::from(head);
    let mut col = head.chars().count();
    for it in items {
        let n = it.chars().count() + 1;
        if col + n > WIDTH {
            out.push_str("\n   ");
            col = 3;
        }
        out.push(' ');
        out.push_str(it);
        col += n;
    }
    out.push('\n');
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
        out.push_str(&format!("  {source} {n}\n"));
    }
    out.push('\n');
    for f in &r.plan.files {
        out.push_str(&format!(
            "  {} {} decl(s), {} lines\n",
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

/// The first line, cut to `width` on a character boundary, with the cut shown.
///
/// The ellipsis is not decoration. A type cut mid-expression that looks whole
/// is read as the whole type, and the reader cannot tell that the part
/// deciding whether the lemma applies was the part removed.
fn first_line(s: &str, width: usize) -> std::borrow::Cow<'_, str> {
    let line = s.lines().next().unwrap_or("");
    let cut = match line.char_indices().nth(width) {
        Some((i, _)) => &line[..i],
        None => return line.into(),
    };
    format!("{cut}…").into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::decl::Span;

    fn hits(rows: Vec<Decl>) -> Hits {
        Hits { rows, truncated: false, empty: None }
    }

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
        let rendered = find(&hits(vec![decl(false)]), false);
        assert!(rendered.contains("[text]"), "got: {rendered}");
        assert!(!find(&hits(vec![decl(true)]), false).contains("[text]"));
    }

    #[test]
    fn a_hit_costs_two_lines_and_no_padding() {
        let r = find(&hits(vec![decl(true), decl(true)]), false);
        assert_eq!(r.lines().count(), 5, "two hits, two lines each, one footer: {r}");
        assert!(!r.contains("\n\n"), "blank separators are paid for on every read: {r}");
        assert!(!r.contains("   "), "no run of padding: {r}");
    }

    #[test]
    fn the_docstring_waits_for_long() {
        let mut d = decl(true);
        d.doc = Some("The exponential is monotone.".into());
        assert!(!find(&hits(vec![d.clone()]), false).contains("monotone"));
        assert!(find(&hits(vec![d]), true).contains("monotone"));
    }

    #[test]
    fn a_truncated_search_says_so_instead_of_looking_complete() {
        let full = find(&hits(vec![decl(true)]), false);
        let cut = find(&Hits { rows: vec![decl(true)], truncated: true, empty: None }, false);
        assert!(full.contains("1 result"));
        assert!(cut.contains("more match"), "got: {cut}");
    }

    #[test]
    fn a_dependency_level_names_its_source_once() {
        let level: Vec<Decl> = ["LE.le", "Real", "Real.exp_monotone"]
            .iter()
            .map(|n| Decl::stub(n, "mathlib", "Mathlib.Order.Defs"))
            .collect();
        let r = by_source(&level);
        assert_eq!(r, "  mathlib: LE.le Real Real.exp_monotone\n");
        assert_eq!(r.matches("mathlib").count(), 1);
    }

    #[test]
    fn a_long_dependency_level_wraps_instead_of_running_off() {
        let names: Vec<String> = (0..40).map(|i| format!("Mathlib.Order.Thing{i}")).collect();
        let level: Vec<Decl> =
            names.iter().map(|n| Decl::stub(n, "mathlib", "Mathlib.Order.Defs")).collect();
        let r = by_source(&level);
        assert!(r.lines().count() > 1, "40 names must not be one line");
        assert!(r.lines().all(|l| l.chars().count() <= 96), "{r}");
        for n in &names {
            assert!(r.contains(n.as_str()), "{n} was dropped");
        }
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
    fn one_invocation_for_several_names_does_not_repeat_a_shared_import() {
        let one = Shown {
            decl: decl(true),
            import: Some("import Mathlib.Analysis.Complex.Exponential".into()),
            source_text: None,
            note: None,
        };
        let two = Shown { decl: decl(true), ..one.clone() };
        let r = show_all(&[one, two], true);
        assert_eq!(r, "import Mathlib.Analysis.Complex.Exponential\n");
    }

    #[test]
    fn show_says_so_when_a_source_cannot_be_imported() {
        let s = Shown { decl: decl(false), import: None, source_text: None, note: None };
        assert!(show(&s, true).contains("not importable"));
    }

    #[test]
    fn cutting_a_long_type_never_splits_a_character() {
        let wide = "≤".repeat(200);
        let cut = first_line(&wide, 10);
        assert_eq!(cut.chars().count(), 11, "ten characters and the mark that says so");
        assert!(cut.ends_with('…'));
    }

    #[test]
    fn a_type_that_fits_is_not_marked_as_cut() {
        assert_eq!(first_line("x ≤ y", 100), "x ≤ y");
    }

    #[test]
    fn an_empty_result_says_so_rather_than_printing_nothing() {
        assert_eq!(find(&hits(vec![]), false), "no match\n");
    }
}
