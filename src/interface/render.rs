//! Turning use-case results into what appears in the terminal.
//!
//! Every result line says whether the row was elaborated. A search that
//! silently mixed compiled and text corpora would be worse than no search, so
//! the marker is not optional and not a verbosity setting.

use crate::application::add::AddReport;
use crate::application::deps::DepsResult;
use crate::application::find::{Asked, Duplicate, Empty, Hits};
use crate::application::ports::Missing;
use crate::application::rdeps::Users;
use crate::application::show::{Shown, Source};
use crate::application::status::{Report, SourceStatus, Stale, Why};
use crate::domain::decl::{ArgHead, Decl};
use crate::domain::lean_core;
use crate::domain::pattern;
use crate::domain::source::SourceKind;
use std::collections::{BTreeMap, BTreeSet};

/// The marker every text row carries.
pub fn mark(d: &Decl) -> &'static str {
    if d.elaborated { "" } else { "  [text]" }
}

fn sorry_mark(d: &Decl) -> &'static str {
    if d.has_sorry { "  [sorry]" } else { "" }
}

/// A pattern with a symbol in it that the parser cannot read.
///
/// This is an empty result rather than an error, because the pattern is not
/// malformed -- it is understood by Lean and not by `dt`. What it must not be
/// is rows: dropping the symbol leaves a pattern that matches more, and the
/// extra rows read as an answer while being about something else. `no match`
/// is the answer that can be acted on, and the symbol is the part to act on.
pub fn unreadable(symbols: &[String]) -> String {
    let list: Vec<String> = symbols.iter().map(|s| format!("`{s}`")).collect();
    format!(
        "no match: {} in the pattern {} as nothing here; searching without {} would answer a \
         wider question — write the constant it stands for instead, or drop that part of the \
         pattern and give it as --uses\n",
        list.join(", "),
        if symbols.len() == 1 { "reads" } else { "read" },
        if symbols.len() == 1 { "it" } else { "them" },
    )
}

/// What a barren flag does not read, for the two flags whose names promise
/// more than they search.
///
/// `--uses X` matching nothing reads as "nothing uses X", and it sent a reader
/// back to grep for a lemma twenty proofs rest on: the flag reads statements.
/// `--text` reads declarations, and a word from a module's header is not in
/// any of them.
fn scope_notes(labels: &[String]) -> String {
    let mut out = String::new();
    if let Some(c) = labels.iter().find_map(|l| l.strip_prefix("--uses ")) {
        out.push_str(&format!(
            "; --uses reads statements only — `dt rdeps {c}` lists the proofs that use it"
        ));
    }
    if labels.iter().any(|l| l.starts_with("--text ")) {
        out.push_str(
            "; --text reads the names, types and docstrings of declarations, not module docstrings",
        );
    }
    out
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
                format!("no match: {} matches nothing on its own{}\n", c[0], scope_notes(c))
            }
            Some(Empty::Barren(c)) => {
                format!("no match: {} match nothing on their own{}\n", c.join(", "), scope_notes(c))
            }
            Some(Empty::Combination { elsewhere }) if elsewhere.is_empty() => {
                "no match: every condition matches on its own; drop one\n".into()
            }
            // The module prefix is the condition to drop, and saying so is only
            // half of it: what the reader wanted was the prefix that would have
            // worked. Four, because a name that spreads wider than that is a
            // name to narrow rather than a place to look.
            Some(Empty::Combination { elsewhere }) => {
                let shown: Vec<String> = elsewhere
                    .iter()
                    .take(4)
                    .map(|(m, n)| match n {
                        1 => m.to_string(),
                        n => format!("{m} ({n})"),
                    })
                    .collect();
                let more = match elsewhere.len().saturating_sub(4) {
                    0 => String::new(),
                    n => format!(", and {n} more"),
                };
                format!(
                    "no match: drop --in — without it the rest matches in {}{}\n",
                    shown.join(", "),
                    more
                )
            }
            // Not "matches nothing on its own", which would be true and would
            // send the reader to correct a prefix that is already correct.
            Some(Empty::NotIndexed { asked, missing: missing @ Missing::Package(pkg) }) => {
                format!(
                    "no match: `{}` is in the lake package `{pkg}`, which is not a source \
                     of this index; {}\n",
                    asked.as_str(),
                    missing.fix()
                )
            }
            // There is a repair to offer now. Core used to be the one corpus
            // with no source to point at, so this line named the toolchain and
            // stopped; `kind = "core"` is two lines of TOML and one command.
            Some(Empty::NotIndexed {
                asked: Asked::Module(m),
                missing: missing @ Missing::Core(tc),
            }) => {
                format!(
                    "no match: `{m}` is a module of Lean core ({tc}), which is not a source \
                     of this index; {}\n",
                    missing.fix()
                )
            }
            // A name says less than a module does: the namespace is core's,
            // the declaration may be anyone's. Claiming the second would be
            // claiming to know what is in a corpus nobody has read.
            Some(Empty::NotIndexed {
                asked: Asked::Name(n),
                missing: missing @ Missing::Core(tc),
            }) => {
                format!(
                    "no match: `{}` is a namespace Lean core declares in, and core ({tc}) is \
                     not a source of this index; {}\n",
                    n.namespace_root(),
                    missing.fix()
                )
            }
            // The word is not misspelled and no condition needs dropping:
            // what it names is spelled differently in the index than it is on
            // the screen, and only the index's spelling can be searched for.
            Some(Empty::Unqualified { written, candidates }) => {
                let (first, rest) = candidates.split_first().expect("a candidate, or no variant");
                let others = match rest.len() {
                    0 => String::new(),
                    _ => format!(
                        "; also {}",
                        rest.iter()
                            .take(2)
                            .map(|n| format!("`{n}`"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                };
                format!(
                    "no match: `{written}` is `{first}` in the index — Lean prints an exported \
                     name without its namespace — and that matches nothing either{others}\n"
                )
            }
            // A pattern is one thing to whoever wrote it, however many
            // conditions it becomes inside, so the answer is about the pattern
            // rather than about which flag to drop. One near miss and not all
            // three: each is a rewrite to try, and they are offered in the
            // order of how little they change.
            Some(Empty::NoSuchShape { under, without, swapped }) => {
                let near = if *swapped {
                    "; the same two sides the other way round do".to_string()
                } else if !under.is_empty() {
                    let shown: Vec<String> = under
                        .iter()
                        .take(3)
                        .map(|(c, n)| match n {
                            1 => format!("`{c}`"),
                            n => format!("`{c}` ({n})"),
                        })
                        .collect();
                    format!("; those arguments go together under {}", shown.join(", "))
                } else if without.len() > 1 {
                    let shown: Vec<String> = without.iter().map(|n| format!("`{n}`")).collect();
                    format!("; each of {} matches without the others", shown.join(", "))
                } else if let Some(n) = without.first() {
                    format!("; it matches with `{n}` written as `_`")
                } else {
                    String::new()
                };
                format!("no match: nothing has that shape{near}\n")
            }
            Some(Empty::NotInShape { absent, together }) => {
                let shown: Vec<String> = absent.iter().map(|n| format!("`{n}`")).collect();
                let what = if *together {
                    format!("{} together", shown.join(" and "))
                } else {
                    shown.join(" or ")
                };
                format!(
                    "no match: the shape matches, but nothing of that shape mentions {what}; a \
                     name inside a side is looked for anywhere in the statement\n"
                )
            }
            // A relation with the pattern's head on one side is the case worth
            // a rewrite: that side is what the reader was after.
            Some(Empty::NamedElsewise { name, shape, on_a_side }) => {
                let concl = shape.concl.as_ref().map_or("_", |c| c.as_str());
                let args: Vec<&str> = shape.args.iter().map(ArgHead::as_str).collect();
                let over = match args.len() {
                    0 => String::new(),
                    _ => format!(" over `{}`", args.join(" ")),
                };
                let rewrite = match pattern::symbol(concl) {
                    Some(sym) if *on_a_side => {
                        format!("; to match one side of it, append ` {sym} _` to the pattern")
                    }
                    _ => String::new(),
                };
                format!(
                    "no match: `{name}` concludes `{concl}`{over}, and a pattern is matched \
                     against the whole conclusion{rewrite}\n"
                )
            }
            Some(Empty::OnlyGenerated) => "no match: only names the compiler generated match \
                 (ctorIdx, congr_simp, …), which are hidden — add --generated to see them\n"
                .into(),
            // Naming a source is not optional in the repair: the dump is out
            // of date and nothing on disk has moved, so a bare `dt refresh`
            // reports that there is nothing to do.
            Some(Empty::InstancesAreDefs) => "no match: no elaborated row carries the kind \
                 `instance`; a dump older than dt 0.20.0 records every instance as `def` — \
                 re-read the source to get them: `dt refresh <source>`\n"
                .into(),
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

/// Who mentions a declaration, one line per module.
///
/// Full names, because the next step is `dt show` on one of them; the module
/// is said once, because it is what repeats.
pub fn rdeps(u: &Users) -> String {
    if u.total == 0 {
        return format!("nothing in the index mentions {}\n", u.root);
    }
    let starred = u.shown.iter().any(|m| m.in_statement);
    let mut out = format!(
        "{}: used by {}{}{}\n",
        u.root,
        u.total,
        match u.total - u.shown.len() {
            0 => String::new(),
            _ => format!(", first {} shown; --limit for more", u.shown.len()),
        },
        if starred { " (* in the statement)" } else { "" },
    );
    let mut groups: Vec<(String, Vec<String>)> = Vec::new();
    for m in &u.shown {
        let d = &m.decl;
        let head = format!("  {}{}:", d.module, mark(d));
        let item = format!("{}{}", d.name, if m.in_statement { "*" } else { "" });
        match groups.last_mut() {
            Some((h, items)) if *h == head => items.push(item),
            _ => groups.push((head, vec![item])),
        }
    }
    for (head, items) in &groups {
        let items: Vec<&str> = items.iter().map(String::as_str).collect();
        out.push_str(&wrapped(head, &items));
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
    // One line and one command. This used to be two lines, split by what
    // reads the source — the build for an elaborated one, the checkout for a
    // text one — because the reader had to run the right half themselves.
    // `dt refresh` picks the half, and with no argument it refreshes exactly
    // the sources this line names, so the advice is the command.
    // Named with the reason, because the two reasons look nothing alike in the
    // table above: a source that moved shows it in the revision column, and one
    // whose rows an older `dt` wrote shows nothing at all — every column of it
    // is what it was, and the rows behind them are not.
    let stale: Vec<&SourceStatus> = rows.iter().filter(|r| r.stale()).collect();
    if !stale.is_empty() {
        let names: Vec<&str> = stale.iter().map(|r| r.name.as_str()).collect();
        // Upgrading `dt` puts every source behind at once and for the same
        // reason. Repeating it per name is five copies of one sentence, so a
        // reason they all share is said once and only a mixed list spells it
        // out row by row.
        let reasons: BTreeSet<&Option<Option<String>>> =
            stale.iter().map(|r| &r.written_by).collect();
        let why = match reasons.iter().next() {
            Some(Some(by)) if reasons.len() == 1 => {
                format!(" — indexed by {}", wrote(by.as_deref()))
            }
            _ => String::new(),
        };
        let listed = match why.is_empty() && reasons.len() > 1 {
            true => stale
                .iter()
                .map(|r| match &r.written_by {
                    Some(by) => format!("{} (indexed by {})", r.name, wrote(by.as_deref())),
                    None => r.name.clone(),
                })
                .collect::<Vec<_>>()
                .join(", "),
            false => names.join(", "),
        };
        out.push_str(&format!("\nbehind: {listed}{why} — re-run `dt refresh`\n"));
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
             is often theirs\n  — add `[[source]]` with `name = \"core\"` and \
             `kind = \"core\"`, then `dt refresh core`\n",
            tc.name,
            lean_core::ROOTS.join(", "),
        ));
    }
    out
}

/// The warning a search prints when the index is behind the source, with its
/// newline.
///
/// It says which value differs, because the previous wording — "`project`
/// moved since it was indexed" — was read as a claim about a path, and the
/// path had not moved. What had changed was the build the project was dumped
/// from, and a reader who could not see that filed the check as broken rather
/// than re-indexing. A revision pair is checkable; "moved" is not.
///
/// The project is the one source whose revision is not a name: it is a
/// fingerprint of the build tree, which nobody can read and nobody pastes into
/// `git show`. So it gets the fact instead of the values.
pub fn stale(s: &Stale, kind: Option<SourceKind>) -> String {
    let id = &s.id;
    let what = match (&s.why, kind) {
        // The rows are as old as the dt that wrote them, and that dt is the
        // value a reader can check: it is printed by `dt --version`.
        (Why::Written { by }, _) => {
            format!("was indexed by {}, and this is dt {}", wrote(by.as_deref()), version())
        }
        (Why::Moved { .. }, Some(SourceKind::Local)) => {
            "was rebuilt since it was indexed".to_string()
        }
        (Why::Moved { indexed, current }, _) => {
            format!("is at {}, the index at {}", short_rev(current), short_rev(indexed))
        }
    };
    format!("dt: `{id}` {what}; rows may be missing — `dt refresh {id}`\n")
}

/// A source that moved while `dt refresh` read it. The index holds the build
/// the read started from, so it is behind already, and the repair is the same
/// refresh once whatever was building has finished.
pub fn moved_while_read(s: &Stale, kind: Option<SourceKind>) -> String {
    let id = &s.id;
    let what = match (&s.why, kind) {
        (Why::Moved { .. }, Some(SourceKind::Local)) => "was rebuilt".to_string(),
        (Why::Moved { indexed, current }, _) => {
            format!("went from {} to {}", short_rev(indexed), short_rev(current))
        }
        (Why::Written { .. }, _) => "changed".to_string(),
    };
    format!(
        "dt: `{id}` {what} while it was being read, so the index is already behind it — \
         `dt refresh {id}` once the build has finished\n"
    )
}

/// Why an argument with spaces in it is not looked up. The shell is the
/// likely cause, so that is what the line explains, and the primes it ate
/// cannot be put back from here: only the reader knows which names had one.
pub fn glued(arg: &str, words: &[&str]) -> String {
    format!(
        "`{arg}` is {} names in one argument, and no Lean name has a space: a `'` in an \
         unquoted shell word starts a quoted string that runs to the next `'`, joining the \
         words between and dropping both primes — pass each name as its own word, in double \
         quotes if it has a prime (\"List.range'_one\")",
        words.len()
    )
}

/// The `dt` that wrote a source's rows. A version too old to have recorded its
/// own is named by what is known about it rather than by a guess: it is every
/// version before the one that started recording, and "an older dt" is the
/// whole of what the index can say.
fn wrote(by: Option<&str>) -> String {
    match by {
        Some(v) => format!("dt {v}"),
        None => "an older dt".to_string(),
    }
}

/// This build's version, as `dt --version` prints it.
fn version() -> &'static str {
    env!("CARGO_PKG_VERSION")
}

/// A revision as short as it can still be read. A git hash is recognisable at
/// seven characters and is what `git show` wants; a toolchain name is not a
/// hash, and cutting `leanprover/lean4:v4.34.0` to `leanpro` loses the only
/// part of it that says anything.
fn short_rev(rev: &str) -> String {
    match rev.len() == 40 && rev.chars().all(|c| c.is_ascii_hexdigit()) {
        true => rev.chars().take(7).collect(),
        false => rev.to_string(),
    }
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
    use crate::domain::decl::{Shape, Span};
    use crate::domain::name::DeclName;

    fn hits(rows: Vec<Decl>) -> Hits {
        Hits { rows, truncated: false, empty: None, read_as: Vec::new() }
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
        let cut = find(
            &Hits { rows: vec![decl(true)], truncated: true, empty: None, read_as: Vec::new() },
            false,
        );
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
            written_by: None,
        }
    }

    /// What brings a source up to date depends on what reads it, and working
    /// that out is the reader's job only if the tool refuses to do it. One
    /// command covers both halves, so the advice names one command and every
    /// source it applies to.
    #[test]
    fn the_repair_named_is_the_one_command_that_reads_either_source() {
        use crate::domain::source::SourceKind;
        let rows =
            [behind("project", SourceKind::Local, true), behind("flt", SourceKind::Git, false)];
        let r = status(&report(&rows), std::path::Path::new("/p/index.db"));
        // Both revisions, which is what the help promises and what a reader
        // needs to see how far behind the index is.
        assert!(r.contains("4f21c8e (now 9ab0d31, stale)"), "{r}");
        assert!(!r.contains("  \n") && !r.ends_with(" \n"), "no row ends in padding: {r:?}");
        assert!(r.contains("behind: project, flt — re-run `dt refresh`"), "{r}");
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

    /// The reader wrote what Lean printed. Telling them it "matches nothing on
    /// its own" sends them to correct a word that is spelled correctly, so the
    /// line says what the index calls it instead.
    #[test]
    fn an_empty_result_on_an_exported_name_says_what_the_index_calls_it() {
        let r = find(
            &Hits {
                rows: Vec::new(),
                truncated: false,
                empty: Some(Empty::Unqualified {
                    written: "inner".into(),
                    candidates: vec![
                        crate::domain::name::DeclName::new("Inner.inner"),
                        crate::domain::name::DeclName::new("Std.HashMap.inner"),
                    ],
                }),
                read_as: Vec::new(),
            },
            false,
        );
        assert!(r.contains("`inner` is `Inner.inner`"), "{r}");
        assert!(r.contains("Std.HashMap.inner"), "the other candidate is worth naming: {r}");
        assert!(!r.contains("matches nothing on its own"), "that is the wrong repair: {r}");
    }

    /// Naming the symbol is the whole point: the pattern was written by
    /// someone who knows what it means, and the only thing they cannot know
    /// is which part of it `dt` did not read.
    #[test]
    fn a_symbol_the_parser_cannot_read_is_named_and_the_repair_offered() {
        let r = unreadable(&["∩".to_string()]);
        assert!(r.starts_with("no match: `∩` in the pattern reads as nothing"), "{r}");
        assert!(r.contains("--uses"), "the repair, not just the complaint: {r}");
        // Two of them are two of them, in one line.
        let r = unreadable(&["∩".to_string(), "×".to_string()]);
        assert!(r.contains("`∩`, `×` in the pattern read as nothing"), "{r}");
        assert_eq!(r.lines().count(), 1, "{r}");
    }

    /// The flag is right and the index is old: the repair is a re-read, and
    /// it has to name a source, because nothing on disk has moved and a bare
    /// `dt refresh` would report that there is nothing to do.
    #[test]
    fn an_instance_search_against_an_old_dump_asks_for_a_re_read() {
        let r = find(
            &Hits {
                rows: Vec::new(),
                truncated: false,
                empty: Some(Empty::InstancesAreDefs),
                read_as: Vec::new(),
            },
            false,
        );
        assert!(r.contains("`instance`"), "{r}");
        assert!(r.contains("dt refresh <source>"), "the repair, not just the complaint: {r}");
        assert!(!r.contains("drop"), "there is no condition to drop: {r}");
    }

    /// "Drop one" is right and unhelpful when the one to drop is `--in`: the
    /// reader already knows the lemma exists and guessed wrong about where it
    /// is kept, and the modules it really lives in are one search away.
    #[test]
    fn an_empty_result_says_where_the_rest_of_the_query_does_match() {
        let empty = |e: Empty| Hits {
            rows: Vec::new(),
            truncated: false,
            empty: Some(e),
            read_as: Vec::new(),
        };
        let r = find(
            &empty(Empty::Combination {
                elsewhere: vec![
                    (crate::domain::name::ModuleName::new("Mathlib.Data.Int.Init"), 4),
                    (
                        crate::domain::name::ModuleName::new(
                            "Mathlib.Algebra.Order.GroupWithZero.Basic",
                        ),
                        3,
                    ),
                ],
            }),
            false,
        );
        assert!(r.contains("drop --in"), "{r}");
        assert!(r.contains("Mathlib.Algebra.Order.GroupWithZero.Basic (3)"), "{r}");

        // With no module in the query there is nothing to name, and the line
        // goes back to saying the only thing it can.
        let plain = find(&empty(Empty::Combination { elsewhere: Vec::new() }), false);
        assert!(plain.contains("every condition matches on its own; drop one"), "{plain}");
        assert!(!plain.contains("--in"), "{plain}");
    }

    /// The reader wrote one pattern, and "drop one condition" is an answer
    /// about flags. What is wanted is the nearest shape that does match.
    #[test]
    fn a_shape_that_matches_nothing_says_what_nearly_does() {
        let empty = |e: Empty| Hits {
            rows: Vec::new(),
            truncated: false,
            empty: Some(e),
            read_as: Vec::new(),
        };
        let shape = |under: Vec<(&str, usize)>, without: Vec<&str>, swapped: bool| {
            find(
                &empty(Empty::NoSuchShape {
                    under: under.into_iter().map(|(c, n)| (DeclName::new(c), n)).collect(),
                    without: without.into_iter().map(DeclName::new).collect(),
                    swapped,
                }),
                false,
            )
        };

        // The cheapest rewrite first: the same sides, written the other way.
        let r = shape(vec![("Eq", 3)], vec!["Finset.sum"], true);
        assert!(r.contains("the other way round"), "{r}");
        assert!(!r.contains("Eq"), "one near miss, the nearest: {r}");

        // Then the right arguments under the wrong relation.
        let r = shape(vec![("HasDerivAt", 4), ("LE.le", 1)], vec!["Real.exp"], false);
        assert!(r.contains("`HasDerivAt` (4), `LE.le`"), "a count of one is not worth a note: {r}");

        // Then which argument to give up on.
        let r = shape(vec![], vec!["Real.log", "Real.sqrt"], false);
        assert!(r.contains("each of `Real.log`, `Real.sqrt` matches without"), "{r}");
        let r = shape(vec![], vec!["Filter.atBot"], false);
        assert!(r.contains("`Filter.atBot` written as `_`"), "{r}");

        // And nothing is offered when nothing is near, which is still not
        // "drop one": there is no flag here to drop.
        let r = shape(vec![], vec![], false);
        assert_eq!(r, "no match: nothing has that shape\n");
    }

    #[test]
    fn a_pattern_answered_by_its_parts_says_which_part() {
        let empty = |e: Empty| {
            find(
                &Hits { rows: Vec::new(), truncated: false, empty: Some(e), read_as: Vec::new() },
                false,
            )
        };
        let names = |ns: &[&str]| ns.iter().map(|n| DeclName::new(*n)).collect::<Vec<_>>();

        let r =
            empty(Empty::NotInShape { absent: names(&["List.take", "List.drop"]), together: true });
        assert!(r.contains("mentions `List.take` and `List.drop` together"), "{r}");
        let r = empty(Empty::NotInShape { absent: names(&["List.drop"]), together: false });
        assert!(r.contains("mentions `List.drop`;"), "{r}");

        let iff = Shape::new(
            Some(DeclName::new("Iff")),
            vec![ArgHead::parse("List.Sublist"), ArgHead::parse("Or")],
        );
        let elsewise = |on_a_side| {
            empty(Empty::NamedElsewise {
                name: DeclName::new("List.sublist_cons_iff"),
                shape: iff.clone(),
                on_a_side,
            })
        };
        let r = elsewise(true);
        assert!(
            r.contains("`List.sublist_cons_iff` concludes `Iff` over `List.Sublist Or`"),
            "{r}"
        );
        assert!(r.contains("append ` ↔ _`"), "{r}");
        assert!(!elsewise(false).contains("append"), "no side to match");

        assert!(empty(Empty::OnlyGenerated).contains("--generated"));

        let r = empty(Empty::Barren(vec!["--uses Real.exp_le_exp".into()]));
        assert!(r.contains("`dt rdeps Real.exp_le_exp`"), "{r}");
        let r = empty(Empty::Barren(vec!["--text crasp".into(), "--in M".into()]));
        assert!(r.contains("not module docstrings"), "{r}");
        assert!(!empty(Empty::Barren(vec!["--in M".into()])).contains(';'));
    }

    #[test]
    fn rdeps_says_each_module_once_and_marks_the_statements() {
        use crate::application::ports::Mention;
        let at = |name: &str, module: &str, in_statement| Mention {
            decl: Decl::stub(name, "mathlib", module),
            in_statement,
        };
        let users = |shown: Vec<Mention>, total| Users { root: DeclName::new("X"), shown, total };

        let r = rdeps(&users(
            vec![at("A.a", "M.A", false), at("A.b", "M.A", true), at("B.c", "M.B", false)],
            3,
        ));
        assert_eq!(r.lines().next(), Some("X: used by 3 (* in the statement)"), "{r}");
        assert_eq!(r.matches("M.A").count(), 1, "{r}");
        assert!(r.contains("A.b*"), "{r}");
        assert!(!r.contains("B.c*"), "{r}");

        let r = rdeps(&users(vec![at("B.c", "M.B", false)], 40));
        assert_eq!(r.lines().next(), Some("X: used by 40, first 1 shown; --limit for more"), "{r}");
        assert_eq!(rdeps(&users(Vec::new(), 0)), "nothing in the index mentions X\n");
    }

    /// `--in Batteries` is not a prefix to correct, and telling the reader it
    /// "matches nothing on its own" sends them to correct it anyway.
    #[test]
    fn an_empty_result_from_an_unindexed_package_names_the_package() {
        let empty = |e: Empty| Hits {
            rows: Vec::new(),
            truncated: false,
            empty: Some(e),
            read_as: Vec::new(),
        };
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
        assert!(r.contains("kind = \"core\""), "and how to index them: {r}");

        let r = status(&with(true), db);
        assert!(r.contains("toolchain: leanprover/lean4:v4.33.1"), "{r}");
        assert!(!r.contains("not indexed"), "nothing to repair, nothing to print: {r}");
    }

    /// The toolchain, and the repair. The repair is the newer half: core was
    /// the one corpus with no source to point at, and `kind = "core"` is what
    /// turned "this is not indexed" into something a reader can act on.
    #[test]
    fn an_empty_result_from_core_names_the_toolchain_and_the_repair() {
        let r = find(
            &Hits {
                rows: Vec::new(),
                truncated: false,
                empty: Some(Empty::NotIndexed {
                    asked: Asked::Module("Init.Data.Int".into()),
                    missing: Missing::Core("leanprover/lean4:v4.33.1".into()),
                }),
                read_as: Vec::new(),
            },
            false,
        );
        assert!(r.contains("Lean core (leanprover/lean4:v4.33.1)"), "{r}");
        assert!(!r.contains("matches nothing"), "that is the wrong repair: {r}");
        assert!(r.contains("`dt refresh core`"), "the repair that does work: {r}");
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
                read_as: Vec::new(),
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

    /// The line a search prints when the index is behind. It has to name the
    /// values, because the reader who saw "moved since it was indexed" checked
    /// the path, found it unmoved, and reported the check as broken.
    #[test]
    fn a_stale_line_says_which_value_differs() {
        let s = Stale {
            id: crate::domain::source::SourceId::new("mathlib"),
            why: Why::Moved {
                indexed: "5ed2965256430c3649e86755f9576b54eca72435".into(),
                current: "4f8b12c56430c3649e86755f9576b54eca724359".into(),
            },
        };
        let line = stale(&s, Some(SourceKind::Lake));
        assert!(line.contains("is at 4f8b12c, the index at 5ed2965"), "{line}");
        assert!(line.contains("`dt refresh mathlib`"), "{line}");
        assert!(!line.contains("moved"), "a revision is not a path: {line}");
    }

    /// The project's revision is a fingerprint of its build tree. Printing two
    /// of them side by side says nothing a reader can act on, so the line says
    /// what happened instead.
    #[test]
    fn the_project_is_rebuilt_not_moved() {
        let s = Stale {
            id: crate::domain::source::SourceId::new("project"),
            why: Why::Moved {
                indexed: "b57d6d7986c61d4a".into(),
                current: "04e1042c1f0b2e55".into(),
            },
        };
        let line = stale(&s, Some(SourceKind::Local));
        assert!(line.contains("`project` was rebuilt since it was indexed"), "{line}");
        assert!(!line.contains("b57d6d7"), "a build fingerprint is not worth reading: {line}");
    }

    #[test]
    fn a_build_that_lands_during_a_refresh_is_named_at_the_end_of_it() {
        let moved = |id: &str| Stale {
            id: crate::domain::source::SourceId::new(id),
            why: Why::Moved {
                indexed: "b57d6d7986c61d4a".into(),
                current: "04e1042c1f0b2e55".into(),
            },
        };
        let line = moved_while_read(&moved("project"), Some(SourceKind::Local));
        assert!(line.contains("`project` was rebuilt while it was being read"), "{line}");
        assert!(line.contains("`dt refresh project` once the build has finished"), "{line}");
        assert!(!line.contains("b57d6d7"), "{line}");
        let mut sha = moved("mathlib");
        sha.why = Why::Moved {
            indexed: "5ed2965256430c3649e86755f9576b54eca72435".into(),
            current: "4f8b12c56430c3649e86755f9576b54eca724359".into(),
        };
        let line = moved_while_read(&sha, Some(SourceKind::Lake));
        assert!(line.contains("went from 5ed2965 to 4f8b12c"), "{line}");
    }

    #[test]
    fn a_glued_argument_says_what_the_shell_did() {
        let arg = "List.range_one List.Perm.mem_iff List.mem_range_1";
        let line = glued(arg, &arg.split(' ').collect::<Vec<_>>());
        assert!(line.contains("is 3 names in one argument"), "{line}");
        assert!(line.contains("dropping both primes"), "{line}");
        assert!(!line.contains("--name"), "a fragment is not worth a search: {line}");
    }

    /// A toolchain is not a hash and must not be cut to seven characters:
    /// `leanpro` is not a version anybody can compare.
    #[test]
    fn a_toolchain_keeps_its_version() {
        let s = Stale {
            id: crate::domain::source::SourceId::new("core"),
            why: Why::Moved {
                indexed: "leanprover/lean4:v4.33.1".into(),
                current: "leanprover/lean4:v4.34.0".into(),
            },
        };
        assert!(stale(&s, Some(SourceKind::Core)).contains("v4.34.0, the index at leanprover"));
    }

    /// The other way an index falls behind, and the one no revision can show:
    /// the source is where it was and the rows in it are not what this build
    /// writes. The line names both versions, because "out of date" without a
    /// pair of values is the wording that was read as a claim about a path and
    /// filed as a bug.
    #[test]
    fn a_stale_line_names_the_dt_that_wrote_the_rows() {
        let by = |v: Option<&str>| Stale {
            id: crate::domain::source::SourceId::new("mathlib"),
            why: Why::Written { by: v.map(str::to_string) },
        };
        let line = stale(&by(Some("0.22.0")), Some(SourceKind::Lake));
        assert!(line.contains("was indexed by dt 0.22.0"), "{line}");
        assert!(line.contains(&format!("this is dt {}", env!("CARGO_PKG_VERSION"))), "{line}");
        assert!(line.contains("`dt refresh mathlib`"), "{line}");
        // A dt too old to have recorded which it was says that much and no
        // more: a version it never wrote down cannot be guessed at.
        assert!(stale(&by(None), Some(SourceKind::Lake)).contains("an older dt"));
    }

    /// `behind:` is the only place the status table can report this, because
    /// every column of such a row is exactly what it was: same revision, same
    /// count, same age. So the reason travels with the name.
    #[test]
    fn the_status_line_says_when_it_is_the_writer_that_is_behind() {
        use crate::domain::source::SourceKind;
        let rows = [SourceStatus {
            current_rev: Some("4f21c8e".into()),
            written_by: Some(Some("0.22.0".into())),
            ..behind("mathlib", SourceKind::Lake, true)
        }];
        let r = status(&report(&rows), std::path::Path::new("/p/index.db"));
        assert!(r.contains("behind: mathlib — indexed by dt 0.22.0 — re-run `dt refresh`"), "{r}");
    }

    /// Upgrading puts every source behind at once, and five copies of one
    /// sentence is not five facts. A reason they all share is said once; a
    /// list where they differ is spelled out, because then it is five facts.
    #[test]
    fn a_reason_every_source_shares_is_said_once() {
        use crate::domain::source::SourceKind;
        let old = |name: &str| SourceStatus {
            current_rev: Some("4f21c8e".into()),
            written_by: Some(None),
            ..behind(name, SourceKind::Lake, true)
        };
        let r = status(&report(&[old("mathlib"), old("core")]), std::path::Path::new("/p/i.db"));
        assert!(r.contains("behind: mathlib, core — indexed by an older dt"), "{r}");

        // One moved and one was written by an older dt: two facts, two notes.
        let mixed = [old("mathlib"), behind("project", SourceKind::Local, true)];
        let r = status(&report(&mixed), std::path::Path::new("/p/i.db"));
        assert!(r.contains("behind: mathlib (indexed by an older dt), project —"), "{r}");
    }
}
