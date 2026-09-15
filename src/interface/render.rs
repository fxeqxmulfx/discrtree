//! Turning use-case results into what appears in the terminal.
//!
//! Every result line says whether the row was elaborated. A search that
//! silently mixed compiled and text corpora would be worse than no search, so
//! the marker is not optional and not a verbosity setting.

use crate::application::add::AddReport;
use crate::application::deps::DepsResult;
use crate::application::find::{Asked, Duplicate, Empty, Hits};
use crate::application::ports::Missing;
use crate::application::show::{Shown, Source};
use crate::application::status::{Report, SourceStatus};
use crate::domain::decl::Decl;
use crate::domain::lean_core;
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
            // Not "matches nothing on its own", which would be true and would
            // send the reader to correct a prefix that is already correct.
            Some(Empty::NotIndexed { asked, missing: Missing::Package(pkg) }) => format!(
                "no match: `{}` is in the lake package `{pkg}`, which is not a source \
                 of this index; add it to discrtree.toml and re-run `dt dump {pkg}` and \
                 `dt index`\n",
                asked.as_str()
            ),
            // No `dt dump` line to offer: core is not a directory under
            // `.lake/packages` that a source can be pointed at in one line, and
            // printing a command that does not work is worse than printing
            // none. `dt status` has the toolchain and the reader has the call.
            Some(Empty::NotIndexed { asked: Asked::Module(m), missing: Missing::Core(tc) }) => {
                format!(
                    "no match: `{m}` is a module of Lean core ({tc}), which is not a source \
                     of this index\n"
                )
            }
            // A name says less than a module does: the namespace is core's,
            // the declaration may be anyone's. Claiming the second would be
            // claiming to know what is in a corpus nobody has read.
            Some(Empty::NotIndexed { asked: Asked::Name(n), missing: Missing::Core(tc) }) => {
                format!(
                    "no match: `{}` is a namespace Lean core declares in, and core ({tc}) is \
                     not a source of this index\n",
                    n.namespace_root()
                )
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
    out.push_str(&at(&s.decl));
    out.push('\n');
    // A generated declaration has no source of its own, so the header has to say
    // where the lines below came from. Without it the type reads like a summary
    // of source that was withheld, rather than the whole of what exists.
    if let Source::Generated { inside, head } = &s.source {
        match inside {
            Some(d) => out.push_str(&format!(
                "  generated inside {}{}; `dt show {}` has the source\n",
                d.name,
                at(d),
                d.name
            )),
            None => out.push_str(&format!("  those lines declare nothing: `{head}`\n")),
        }
    }
    out.push('\n');
    match &s.source {
        Source::Text(t) => {
            out.push_str(t);
            out.push('\n');
        }
        Source::Generated { .. } => out.push_str(&format!("{}\n", s.decl.ty)),
        Source::Missing(n) => {
            out.push_str(&format!("-- source not available: {n}\n-- type: {}\n", s.decl.ty))
        }
    }
    out
}

/// `:92-94`, or nothing when the index has no range.
fn at(d: &Decl) -> String {
    d.span.map(|s| format!(":{}-{}", s.start, s.end)).unwrap_or_default()
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

pub fn status(report: &Report, db: &std::path::Path) -> String {
    let rows = &report.sources;
    let mut out = format!("index: {}\n", db.display());
    if let Some(tc) = &report.toolchain {
        out.push_str(&format!("toolchain: {}\n", tc.name));
    }
    out.push('\n');
    // No width on the last column. It is the one that varies, and padding it
    // buys nothing but trailing spaces on every row of every run.
    out.push_str(&format!(
        "{:<14} {:<7} {:<12} {:<12} {:>12}  {:<8} {}\n",
        "source", "kind", "elaborated", "importable", "declarations", "indexed", "revision"
    ));
    for r in rows {
        out.push_str(&format!(
            "{:<14} {:<7} {:<12} {:<12} {:>12}  {:<8} {}\n",
            r.name,
            r.kind.as_str(),
            r.elaborated,
            r.importable,
            r.decls,
            r.age.map_or_else(|| "never".into(), age),
            revision(r),
        ));
    }
    let total: usize = rows.iter().map(|r| r.decls).sum();
    out.push_str(&format!("\n{total} declarations indexed\n"));
    if rows.iter().any(|r| r.decls == 0) {
        out.push_str("\nA source with no declarations has not been dumped or scanned yet.\n");
    }
    // The lines worth spending on: an index that has fallen behind answers
    // with confidence and is wrong, which is the failure this tool exists to
    // prevent, not to commit.
    //
    // Two lines rather than one because what brings a source up to date is
    // whatever reads it, and that differs: an elaborated source is read from
    // the build by `dt dump`, a text source from the checkout by `dt fetch`.
    // Printing both commands for both was advice nobody could act on without
    // first working out which half applied to them.
    let stale = |elaborated: bool| -> Vec<&str> {
        rows.iter()
            .filter(|r| r.stale() && r.elaborated == elaborated)
            .map(|r| r.name.as_str())
            .collect()
    };
    for (which, names, fix) in [
        ("build", stale(true), "`dt dump` and `dt index`"),
        ("checkout", stale(false), "`dt fetch` and `dt index`"),
    ] {
        if !names.is_empty() {
            out.push_str(&format!("\nbehind the {which}: {} — re-run {fix}\n", names.join(", ")));
        }
    }
    // The gap no row above can show. A project declares Mathlib and stops, and
    // everything Mathlib is built on is importable from the project already and
    // in no search — so `no match` for a Batteries lemma reads as "nobody has
    // proved this", and the reader writes it again. Naming the packages is the
    // whole repair: adding one is the reader's call, and a tool that guessed
    // would be dumping gigabytes nobody asked for.
    if !report.unindexed.is_empty() {
        let names: Vec<&str> = report.unindexed.iter().map(|p| p.name.as_str()).collect();
        out.push_str(&format!(
            "\nnot indexed: {}\n  — lake packages the build resolved; \
             add one as a `lake` source to search it\n",
            names.join(", ")
        ));
    }
    // And the corpus under all of them. Core has no directory to be listed
    // from, which is exactly why it has to be said out loud: a reader who sees
    // nothing here reads `no match` on an `Int` lemma as proof that nobody has
    // proved it, and the lemma is in `Init/Data/Int/Order.lean`.
    if let Some(tc) = &report.toolchain
        && !tc.indexed
    {
        out.push_str(&format!(
            "\nnot indexed: Lean core ({})\n  — {} live in the toolchain, not under \
             `.lake/packages`; a `no match` under `Int.`, `Nat.`, `List.` or `Array.` \
             is often theirs\n",
            tc.name,
            lean_core::ROOTS.join(", "),
        ));
    }
    out
}

/// The revision the index was built from, and — when the source has moved
/// since — the one it is at now. Both, because "stale" alone says a re-dump is
/// due and nothing else, while the pair says how far behind and against what:
/// the second value is what `git log A..B` wants, and for the project it is the
/// build fingerprint that tells two rebuilds apart. Seven characters each,
/// which is what a person pastes into `git show`.
fn revision(r: &SourceStatus) -> String {
    let short = |s: &String| s.chars().take(7).collect::<String>();
    match (&r.indexed_rev, &r.current_rev) {
        (Some(was), Some(now)) if was != now => {
            format!("{} (now {}, stale)", short(was), short(now))
        }
        (Some(was), _) => short(was),
        (None, _) => "-".into(),
    }
}

/// An age, not a timestamp: the reader wants to know whether to re-index, and
/// a date makes them do the subtraction first.
fn age(secs: u64) -> String {
    match secs {
        s if s < 90 => "just now".into(),
        s if s < 5400 => format!("{}m ago", s / 60),
        s if s < 172_800 => format!("{}h ago", s / 3600),
        s => format!("{}d ago", s / 86_400),
    }
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

    /// A status report of these sources and no unindexed packages.
    fn report(sources: &[SourceStatus]) -> Report {
        Report { sources: sources.to_vec(), unindexed: Vec::new(), toolchain: None }
    }

    fn behind(
        name: &str,
        kind: crate::domain::source::SourceKind,
        elaborated: bool,
    ) -> SourceStatus {
        SourceStatus {
            name: name.into(),
            kind,
            elaborated,
            importable: true,
            decls: 718,
            indexed_rev: Some("4f21c8e".into()),
            current_rev: Some("9ab0d31".into()),
            age: Some(3600),
        }
    }

    /// What brings a source up to date depends on what reads it. Telling
    /// somebody to `dt fetch` the project they are writing is advice they
    /// cannot follow, and advice nobody can follow is how a warning gets
    /// filtered out of a terminal.
    #[test]
    fn the_repair_named_is_the_one_that_reads_the_source() {
        use crate::domain::source::SourceKind;
        let rows =
            [behind("project", SourceKind::Local, true), behind("flt", SourceKind::Git, false)];
        let r = status(&report(&rows), std::path::Path::new("/p/index.db"));
        // Both revisions, which is what the help promises and what a reader
        // needs to see how far behind the index is.
        assert!(r.contains("4f21c8e (now 9ab0d31, stale)"), "{r}");
        assert!(!r.contains("  \n") && !r.ends_with(" \n"), "no row ends in padding: {r:?}");
        assert!(r.contains("behind the build: project — re-run `dt dump` and `dt index`"), "{r}");
        assert!(r.contains("behind the checkout: flt — re-run `dt fetch` and `dt index`"), "{r}");
        // A source that is where it was is not named at all.
        let current = [SourceStatus {
            current_rev: Some("4f21c8e".into()),
            ..behind("mathlib", SourceKind::Lake, true)
        }];
        assert!(!status(&report(&current), std::path::Path::new("/p/index.db")).contains("behind"));
    }

    /// The gap a table of fresh sources cannot show. Reported at all, because
    /// until it was there was no command in the tool that would say a search
    /// had never covered the package it was about.
    #[test]
    fn packages_no_source_covers_are_named_with_the_repair() {
        use crate::application::ports::Package;
        let pkg = |n: &str| Package { name: n.into(), roots: vec![n.to_uppercase()] };
        let r = status(
            &Report {
                sources: Vec::new(),
                unindexed: vec![pkg("batteries"), pkg("aesop")],
                toolchain: None,
            },
            std::path::Path::new("/p/index.db"),
        );
        assert!(r.contains("not indexed: batteries, aesop"), "{r}");
        assert!(r.contains("`lake` source"), "the repair, not just the complaint: {r}");
        // Silent when there is nothing to report: a line that prints on every
        // run is a line that is read on none.
        assert!(!status(&report(&[]), std::path::Path::new("/p/index.db")).contains("not indexed"));
    }

    /// `--in Batteries` is not a prefix to correct, and telling the reader it
    /// "matches nothing on its own" sends them to correct it anyway.
    #[test]
    fn an_empty_result_from_an_unindexed_package_names_the_package() {
        let empty = |e: Empty| Hits { rows: Vec::new(), truncated: false, empty: Some(e) };
        let r = find(
            &empty(Empty::NotIndexed {
                asked: Asked::Module("Batteries".into()),
                missing: Missing::Package("batteries".into()),
            }),
            false,
        );
        assert!(r.contains("lake package `batteries`"), "{r}");
        assert!(r.contains("not a source"), "{r}");
        assert!(!r.contains("matches nothing"), "that is the wrong repair: {r}");
    }

    /// Core has no directory to be listed from, which is why the line has to
    /// exist at all: without it a reader sees a table of fresh sources and
    /// concludes the search covered everything importable.
    #[test]
    fn an_unindexed_core_is_named_in_the_report_and_an_indexed_one_is_not() {
        use crate::application::ports::Toolchain;
        let with = |indexed: bool| Report {
            sources: Vec::new(),
            unindexed: Vec::new(),
            toolchain: Some(Toolchain { name: "leanprover/lean4:v4.33.1".into(), indexed }),
        };
        let db = std::path::Path::new("/p/index.db");
        let r = status(&with(false), db);
        assert!(r.contains("toolchain: leanprover/lean4:v4.33.1"), "named either way: {r}");
        assert!(r.contains("not indexed: Lean core"), "{r}");
        assert!(r.contains("Init"), "the roots a source would have to import: {r}");

        let r = status(&with(true), db);
        assert!(r.contains("toolchain: leanprover/lean4:v4.33.1"), "{r}");
        assert!(!r.contains("not indexed"), "nothing to repair, nothing to print: {r}");
    }

    /// No `dt dump` line here: core is not a directory a source can be pointed
    /// at in one line, and a command that does not work is worse than none.
    #[test]
    fn an_empty_result_from_core_names_the_toolchain() {
        let r = find(
            &Hits {
                rows: Vec::new(),
                truncated: false,
                empty: Some(Empty::NotIndexed {
                    asked: Asked::Module("Init.Data.Int".into()),
                    missing: Missing::Core("leanprover/lean4:v4.33.1".into()),
                }),
            },
            false,
        );
        assert!(r.contains("Lean core (leanprover/lean4:v4.33.1)"), "{r}");
        assert!(!r.contains("matches nothing"), "that is the wrong repair: {r}");
        assert!(!r.contains("dt dump"), "there is no one-line dump to offer: {r}");
    }

    /// A name says less than a module does, and the line has to say less too:
    /// the namespace is core's, the declaration may be anyone's.
    #[test]
    fn an_empty_name_search_from_core_names_the_namespace_not_the_declaration() {
        let r = find(
            &Hits {
                rows: Vec::new(),
                truncated: false,
                empty: Some(Empty::NotIndexed {
                    asked: Asked::Name(crate::domain::name::DeclName::new("Int.emod_emod_of_dvd")),
                    missing: Missing::Core("leanprover/lean4:v4.33.1".into()),
                }),
            },
            false,
        );
        assert!(r.contains("`Int` is a namespace"), "{r}");
        assert!(!r.contains("emod_emod_of_dvd"), "the claim is about the namespace: {r}");
        assert!(!r.contains("module of Lean core"), "nothing said a module was asked for: {r}");
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
            source: Source::Text("theorem exp_le_exp : True := trivial".into()),
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
            source: Source::Missing("no range".into()),
        };
        let two = Shown { decl: decl(true), ..one.clone() };
        let r = show_all(&[one, two], true);
        assert_eq!(r, "import Mathlib.Analysis.Complex.Exponential\n");
    }

    #[test]
    fn show_says_so_when_a_source_cannot_be_imported() {
        let s =
            Shown { decl: decl(false), import: None, source: Source::Missing("no range".into()) };
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
