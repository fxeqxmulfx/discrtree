//! The use cases against test doubles for every port. What is checked here is
//! the behaviour the plan names: the import line `dt show` prints, the
//! importable frontier that makes `dt add` finite, and the refusal to present
//! guessed dependencies as exact ones.

mod support;

use discrtree::application::add::Add;
use discrtree::application::deps::{Deps, DepsResult};
use discrtree::application::find::{Dup, Empty, Find};
use discrtree::application::ports::Workspace;
use discrtree::application::show::Show;
use discrtree::application::status::Status;
use discrtree::domain::decl::Span;
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use std::path::PathBuf;
use support::{FakeFiles, FakeRepo, FakeRevisions, FakeWriter, sources, theorem};

fn workspace() -> Workspace {
    Workspace {
        sources: sources(),
        vendor_dir: PathBuf::from("/p/src/Transformer/Vendor"),
        vendor_module: ModuleName::new("Transformer.Vendor"),
        namespace: "Transformer".into(),
    }
}

/// `top` (not importable) rests on `mid` (not importable), which rests on
/// `Real.exp_le_exp` in Mathlib (importable). The Mathlib subtree is exactly
/// what must collapse into an import.
fn repo() -> FakeRepo {
    let mut top = theorem("Other.top", "other", "Other.Main", "Eq", &["Other.mid"]);
    top.span = Some(Span::new(1, 2));
    let mut mid = theorem("Other.mid", "other", "Other.Helper", "Eq", &["Real.exp_le_exp"]);
    mid.span = Some(Span::new(1, 2));
    let mut leaf =
        theorem("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Exp", "LE.le", &["Real.exp"]);
    leaf.ty = "Real.exp x ≤ Real.exp y ↔ x ≤ y".into();
    leaf.span = Some(Span::new(316, 317));
    let mut text = theorem("FLT.guessed", "flt", "FLT.Basic", "Eq", &["Real.exp_le_exp"]);
    text.elaborated = false;
    text.span = Some(Span::new(1, 2));
    // `Real.exp` itself, because an identifier only counts as evidence about
    // what a statement is about once the index confirms it names something.
    let mut exp = theorem("Real.exp", "mathlib", "Mathlib.Analysis.Exp", "Real", &[]);
    exp.kind = discrtree::domain::decl::DeclKind::Def;
    exp.consts = Vec::new();
    FakeRepo { decls: vec![top, mid, leaf, text, exp] }
}

fn files() -> FakeFiles {
    FakeFiles::new()
        .with("other", "Other.Main", "theorem top : True :=\n  trivial\n")
        .with("other", "Other.Helper", "theorem mid : True :=\n  trivial\n")
        .with(
            "mathlib",
            "Mathlib.Analysis.Exp",
            &("\n".repeat(315) + "theorem exp_le_exp : True :=\n  trivial\n"),
        )
        .with("flt", "FLT.Basic", "theorem guessed : True :=\n  trivial\n")
}

#[test]
fn show_gives_the_import_that_actually_provides_the_declaration() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let shown = Show { repo: &repo, files: &files, workspace: &ws }
        .run(&DeclName::new("Real.exp_le_exp"))
        .unwrap();
    assert_eq!(shown.import.as_deref(), Some("import Mathlib.Analysis.Exp"));
    assert_eq!(shown.source_text.as_deref(), Some("theorem exp_le_exp : True :=\n  trivial"));
}

#[test]
fn show_offers_no_import_for_a_source_that_cannot_be_imported() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let shown = Show { repo: &repo, files: &files, workspace: &ws }
        .run(&DeclName::new("FLT.guessed"))
        .unwrap();
    assert!(shown.import.is_none(), "a text corpus is not on the import path");
}

#[test]
fn show_says_which_name_it_could_not_find() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let err = Show { repo: &repo, files: &files, workspace: &ws }
        .run(&DeclName::new("No.such"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("No.such") && err.contains("dt find"), "got: {err}");
}

#[test]
fn deps_lists_one_level_at_a_time() {
    let (repo, ws) = (repo(), workspace());
    let result =
        Deps { repo: &repo, workspace: &ws }.run(&DeclName::new("Other.top"), Some(2)).unwrap();
    match result {
        DepsResult::Levels { levels, approximate, .. } => {
            assert!(!approximate, "an elaborated root has exact dependencies");
            assert_eq!(
                levels[0].iter().map(|d| d.name.to_string()).collect::<Vec<_>>(),
                ["Other.mid"]
            );
            assert_eq!(
                levels[1].iter().map(|d| d.name.to_string()).collect::<Vec<_>>(),
                ["Real.exp_le_exp"]
            );
        }
        _ => panic!("asked for levels"),
    }
}

#[test]
fn deps_of_a_text_row_are_reported_as_approximate() {
    // The whole invariant in one assertion: a guessed list must never be
    // presented as the set of constants a proof term uses.
    let (repo, ws) = (repo(), workspace());
    let result =
        Deps { repo: &repo, workspace: &ws }.run(&DeclName::new("FLT.guessed"), Some(1)).unwrap();
    match result {
        DepsResult::Levels { approximate, .. } => assert!(approximate),
        _ => panic!("asked for levels"),
    }
}

#[test]
fn deps_with_no_depth_reports_the_size_rather_than_the_contents() {
    let (repo, ws) = (repo(), workspace());
    match (Deps { repo: &repo, workspace: &ws }).run(&DeclName::new("Other.top"), None).unwrap() {
        DepsResult::Summary { stats, .. } => assert!(stats.total >= 2, "got {}", stats.total),
        _ => panic!("asked for a summary"),
    }
}

#[test]
fn add_collapses_an_importable_dependency_into_one_import_line() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let report = Add { repo: &repo, files: &files, workspace: &ws }
        .plan(&DeclName::new("Other.top"))
        .unwrap();

    assert_eq!(
        report.frontier.imports.iter().map(|m| m.import_line()).collect::<Vec<_>>(),
        ["import Mathlib.Analysis.Exp"]
    );
    let copied: Vec<String> =
        report.plan.files.iter().flat_map(|f| f.decls.iter().map(|d| d.name.to_string())).collect();
    assert!(copied.contains(&"Other.top".to_string()));
    assert!(copied.contains(&"Other.mid".to_string()));
    assert!(
        !copied.contains(&"Real.exp_le_exp".to_string()),
        "a declaration reachable by an import is never copied"
    );
}

#[test]
fn add_of_a_mathlib_declaration_is_one_import_and_nothing_else() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let report = Add { repo: &repo, files: &files, workspace: &ws }
        .plan(&DeclName::new("Real.exp_le_exp"))
        .unwrap();
    assert!(report.is_import_only(), "the correct answer, not a degenerate one");
    assert_eq!(
        report.frontier.imports.iter().map(|m| m.import_line()).collect::<Vec<_>>(),
        ["import Mathlib.Analysis.Exp"]
    );
}

#[test]
fn a_dry_run_writes_nothing() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let report = Add { repo: &repo, files: &files, workspace: &ws }
        .plan(&DeclName::new("Other.top"))
        .unwrap();
    assert!(report.written.is_empty() && report.registered.is_empty());
}

#[test]
fn writing_emits_provenance_the_source_text_and_an_aggregator_entry() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let mut writer = FakeWriter::default();
    let report = Add { repo: &repo, files: &files, workspace: &ws }
        .write(&DeclName::new("Other.top"), &mut writer, false)
        .unwrap();

    assert_eq!(writer.files.len(), report.written.len());
    let all: String = writer.files.iter().map(|(_, t)| t.as_str()).collect();
    assert!(all.contains("Source:"), "every vendored file states where it came from");
    assert!(all.contains("theorem top"), "the declaration is copied verbatim");
    assert!(
        !writer.imports.is_empty(),
        "a module not in the aggregator is not built, so registering it is not optional"
    );
}

#[test]
fn find_refuses_a_query_that_constrains_nothing() {
    let repo = repo();
    let err = Find { repo: &repo }.run(&Query::new()).unwrap_err().to_string();
    assert!(err.contains("nothing to search for"), "got: {err}");
}

#[test]
fn find_returns_at_most_the_limit() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("o".into());
    q.limit = 1;
    assert_eq!(Find { repo: &repo }.run(&q).unwrap().rows.len(), 1);
}

/// The two empty results need opposite repairs, so they must not read alike.
/// A condition that matches nothing on its own is a typo to be edited; a
/// combination that matches nothing is a condition to be dropped. Telling them
/// apart from outside costs a search each, which is the whole reason the use
/// case answers it.
#[test]
fn an_empty_search_says_which_condition_is_impossible() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("top".into());
    q.module = Some("Nowhere".into());
    match (Find { repo: &repo }).run(&q).unwrap().empty {
        Some(Empty::Barren(c)) => assert_eq!(c, vec!["--in Nowhere".to_string()]),
        other => panic!("expected the module condition to be blamed, got {other:?}"),
    }
}

#[test]
fn an_empty_search_over_conditions_that_each_match_blames_none_of_them() {
    let repo = repo();
    let mut q = Query::new();
    // `Other.top` exists and `Mathlib.Analysis.Exp` exists; nothing is both.
    q.name = Some("top".into());
    q.module = Some("Mathlib.Analysis.Exp".into());
    assert_eq!(Find { repo: &repo }.run(&q).unwrap().empty, Some(Empty::Combination));
}

/// With one condition there is nothing to diagnose, and probing it would only
/// repeat the query back. The probes are skipped rather than answered.
#[test]
fn a_single_condition_is_not_diagnosed() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("zzz".into());
    assert_eq!(Find { repo: &repo }.run(&q).unwrap().empty, Some(Empty::Plain));
}

#[test]
fn a_search_that_matches_is_not_diagnosed_at_all() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("top".into());
    assert_eq!(Find { repo: &repo }.run(&q).unwrap().empty, None);
}

#[test]
fn dup_reports_a_local_declaration_upstream_already_has() {
    let repo = repo();
    let files = files();
    let dir = support::TempDir::new("dup");
    let path = dir.write(
        "Mine.lean",
        "theorem my_exp_le (x y : ℝ) : Real.exp x ≤ Real.exp y :=\n  Real.exp_le_exp.mpr h\n",
    );
    let dups = Dup { repo: &repo, files: &files, local: SourceId::new("other"), threshold: 0.1 }
        .run(&path, &ModuleName::new("Transformer.Mine"))
        .unwrap();
    assert!(
        dups.iter().any(|d| d.candidates.iter().any(|c| c.decl.name.as_str() == "Real.exp_le_exp")),
        "got: {:?}",
        dups.iter().map(|d| d.local.name.to_string()).collect::<Vec<_>>()
    );
}

#[test]
fn status_shows_a_configured_source_that_has_nothing_indexed() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::default();
    let rows = Status { repo: &repo, revisions: &revs, workspace: &ws, now: 0 }.run().unwrap();
    assert_eq!(rows.len(), 3);
    let mathlib = rows.iter().find(|r| r.name == "mathlib").unwrap();
    assert!(mathlib.elaborated && mathlib.importable);
    assert_eq!(mathlib.decls, 2);
    let flt = rows.iter().find(|r| r.name == "flt").unwrap();
    assert!(!flt.elaborated && !flt.importable);
}

/// A source is stale when the index remembers one revision and the checkout is
/// at another. A revision nobody can read is not a mismatch: a source with no
/// VCS would otherwise be reported as behind on every run, and a warning that
/// is always on is a warning nobody reads.
#[test]
fn status_reports_a_source_the_checkout_has_moved_past() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::at(&[("mathlib", "bbbbbbb"), ("flt", "ccccccc")]);
    let rows = Status { repo: &repo, revisions: &revs, workspace: &ws, now: 0 }.run().unwrap();
    // The fake repo remembers nothing, so nothing can be behind anything.
    assert!(!rows.iter().any(|r| r.stale()), "nothing recorded cannot be stale");
    assert_eq!(
        rows.iter().find(|r| r.name == "mathlib").unwrap().current_rev.as_deref(),
        Some("bbbbbbb")
    );
}

/// The help is the only documentation a program driving this tool will read,
/// so the load-bearing parts of it are pinned here. `debug_assert` is clap's
/// own check that the definition is coherent: conflicting flags, duplicate
/// short options, a required argument sitting after an optional one.
#[test]
fn the_help_says_the_things_that_matter() {
    use clap::CommandFactory;
    let mut cli = discrtree::interface::cli::Cli::command();
    cli.build();

    let top = cli.render_long_help().to_string();
    // A first run has to be done in order, and the order is not guessable.
    assert!(top.contains("dt init"), "the setup order belongs on the first screen:\n{top}");
    assert!(top.contains("[text]"), "the elaborated/text invariant does too:\n{top}");

    let find = cli
        .find_subcommand_mut("find")
        .expect("find is a subcommand")
        .render_long_help()
        .to_string();
    // The pattern language exists nowhere else: without an example in the help
    // it can only be discovered by guessing, one failed invocation at a time.
    for expected in ["Real.exp _ ≤ _", "--elaborated", "`dt status` lists them"] {
        assert!(find.contains(expected), "`dt find --help` must mention {expected}:\n{find}");
    }
}

/// An argument with no description is an argument that has to be guessed at.
/// Four commands had blank positionals, which is the most expensive kind:
/// `dt deps <NAME>` does not say whether NAME is a module or a declaration.
#[test]
fn every_argument_is_described() {
    use clap::CommandFactory;
    let mut cli = discrtree::interface::cli::Cli::command();
    cli.build();
    for sub in cli.get_subcommands_mut() {
        if sub.get_name() == "help" {
            continue;
        }
        assert!(sub.get_about().is_some(), "`dt {}` has no description", sub.get_name());
        for arg in sub.get_arguments() {
            assert!(
                arg.get_help().is_some() || arg.get_long_help().is_some(),
                "`dt {} {}` has no description",
                sub.get_name(),
                arg.get_id()
            );
        }
    }
}

/// The skill is what an agent loads instead of reading eleven `--help`
/// screens, so its whole value is that it is cheap. Past about 2 KB it stops
/// being cheaper than the thing it replaces.
#[test]
fn the_skill_is_short_and_well_formed() {
    let skill = include_str!("../.claude/skills/discrtree/SKILL.md");
    assert!(skill.len() < 2048, "the skill is {} bytes; keep it under 2048", skill.len());

    let (frontmatter, body) = skill
        .strip_prefix("---\n")
        .and_then(|s| s.split_once("\n---\n"))
        .expect("the skill opens with YAML frontmatter");
    assert!(frontmatter.contains("name: discrtree"), "{frontmatter}");
    // The description is the only part always in context: it is what decides
    // whether the skill gets loaded at all, so it has to say when to.
    assert!(frontmatter.contains("description: "), "{frontmatter}");
    assert!(frontmatter.contains("Lean"), "the description must say what corpus: {frontmatter}");

    // The invariant an agent gets wrong without being told.
    assert!(body.contains("[text]"), "the skill must carry the one invariant:\n{body}");
}
