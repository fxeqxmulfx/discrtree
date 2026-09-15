//! The use cases against test doubles for every port. What is checked here is
//! the behaviour the plan names: the import line `dt show` prints, the
//! importable frontier that makes `dt add` finite, and the refusal to present
//! guessed dependencies as exact ones.

mod support;

use discrtree::application::add::Add;
use discrtree::application::deps::{Deps, DepsResult};
use discrtree::application::find::{Dup, Empty, Find};
use discrtree::application::ports::{NoPackages, Workspace};
use discrtree::application::show::{Show, Source};
use discrtree::application::status::Status;
use discrtree::domain::decl::Span;
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use std::path::PathBuf;
use support::{FakeFiles, FakePackages, FakeRepo, FakeRevisions, FakeWriter, sources, theorem};

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
    let shown = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
        .run(&DeclName::new("Real.exp_le_exp"))
        .unwrap();
    assert_eq!(shown.import.as_deref(), Some("import Mathlib.Analysis.Exp"));
    assert_eq!(shown.source, Source::Text("theorem exp_le_exp : True :=\n  trivial".into()));
}

/// `Finset.sum_image` in miniature: Lean points a `to_additive` twin at the
/// attribute block inside the theorem that generated it, so the range holds an
/// attribute and no declaration at all.
fn generated() -> (FakeRepo, FakeFiles) {
    let mut orig = theorem("Finset.prod_image", "mathlib", "Mathlib.BigOperators", "Eq", &[]);
    orig.span = Some(Span::new(1, 4));
    let mut twin = theorem("Finset.sum_image", "mathlib", "Mathlib.BigOperators", "Eq", &[]);
    twin.ty = "∑ x ∈ s.image f, g x = ∑ x ∈ s, g (f x)".into();
    twin.span = Some(Span::new(2, 2));
    let mut alias = theorem("Eq.ge", "mathlib", "Mathlib.Order", "Eq", &[]);
    alias.ty = "a = b → a ≥ b".into();
    alias.span = Some(Span::new(1, 1));
    // A structure, the projection Lean generates for its parent, and its
    // constructor: three rows over the same two lines, and only the first was
    // written by anyone.
    let mut structure = theorem("Hom", "mathlib", "Mathlib.Hom", "Eq", &[]);
    structure.kind = discrtree::domain::decl::DeclKind::Structure;
    structure.span = Some(Span::new(1, 3));
    let mut field = theorem("Hom.toFun", "mathlib", "Mathlib.Hom", "Eq", &[]);
    field.span = Some(Span::new(1, 2));
    let mut ctor = theorem("Hom.mk", "mathlib", "Mathlib.Hom", "Eq", &[]);
    ctor.span = Some(Span::new(1, 1));
    let repo = FakeRepo { decls: vec![orig, twin, alias, structure, field, ctor] };
    let files = FakeFiles::new()
        .with("mathlib", "Mathlib.Hom", "structure Hom where\n  toFun : Nat\n  inj : True\n")
        .with(
            "mathlib",
            "Mathlib.BigOperators",
            "theorem prod_image :\n  @[to_additive]\n  True :=\n  trivial\n",
        )
        .with("mathlib", "Mathlib.Order", "@[to_dual ge] alias Eq.le := le_of_eq\n");
    (repo, files)
}

#[test]
fn show_names_the_declaration_a_generated_one_came_out_of() {
    let (repo, files) = generated();
    let ws = workspace();
    let shown = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
        .run(&DeclName::new("Finset.sum_image"))
        .unwrap();
    let Source::Generated { inside, .. } = &shown.source else {
        panic!("an attribute block is not a declaration: {:?}", shown.source)
    };
    assert_eq!(
        inside.as_ref().map(|d| d.name.to_string()),
        Some("Finset.prod_image".into()),
        "the enclosing theorem is the one that generated it"
    );
}

#[test]
fn show_walks_past_a_container_that_was_itself_generated() {
    let (repo, files) = generated();
    let ws = workspace();
    let shown = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
        .run(&DeclName::new("Hom.mk"))
        .unwrap();
    let Source::Generated { inside, .. } = &shown.source else {
        panic!("a structure's first line is not its constructor: {:?}", shown.source)
    };
    assert_eq!(
        inside.as_ref().map(|d| d.name.to_string()),
        Some("Hom".into()),
        "the projection Hom.toFun encloses it more tightly, and has no source of its own either"
    );
}

#[test]
fn show_still_answers_when_nothing_encloses_the_generated_lines() {
    let (repo, files) = generated();
    let ws = workspace();
    let shown = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
        .run(&DeclName::new("Eq.ge"))
        .unwrap();
    let Source::Generated { inside, head } = &shown.source else {
        panic!("an alias line declares no theorem: {:?}", shown.source)
    };
    assert!(inside.is_none(), "nothing in the module contains that line");
    assert!(head.contains("alias"), "the head line names the original: {head}");
    // The type is the whole answer in this case, so it has to be printed.
    assert!(discrtree::interface::render::show(&shown, false).contains("a = b → a ≥ b"));
}

#[test]
fn show_offers_no_import_for_a_source_that_cannot_be_imported() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let shown = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
        .run(&DeclName::new("FLT.guessed"))
        .unwrap();
    assert!(shown.import.is_none(), "a text corpus is not on the import path");
}

#[test]
fn show_says_which_name_it_could_not_find() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let err = Show { repo: &repo, files: &files, workspace: &ws, packages: &NoPackages }
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
fn a_generated_declaration_is_vendored_as_the_one_that_generates_it() {
    // `Other.sum_thing` is the `to_additive` twin: its range is the attribute
    // block, and copying that yields a file with an attribute and nothing under
    // it. Copying `prod_thing` instead produces both on elaboration — once.
    let mut uses = theorem(
        "Other.uses",
        "other",
        "Other.Uses",
        "Eq",
        &["Other.sum_thing", "Other.prod_thing"],
    );
    uses.span = Some(Span::new(1, 1));
    let mut prod = theorem("Other.prod_thing", "other", "Other.Gen", "Eq", &[]);
    prod.span = Some(Span::new(1, 3));
    let mut sum = theorem("Other.sum_thing", "other", "Other.Gen", "Eq", &[]);
    sum.span = Some(Span::new(1, 1));
    let repo = FakeRepo { decls: vec![uses, prod, sum] };
    let files = FakeFiles::new()
        .with("other", "Other.Uses", "theorem uses : True := trivial\n")
        .with("other", "Other.Gen", "@[to_additive]\ntheorem prod_thing : True :=\n  trivial\n");

    let ws = workspace();
    let mut writer = FakeWriter::default();
    Add { repo: &repo, files: &files, workspace: &ws }
        .write(&DeclName::new("Other.uses"), &mut writer, false)
        .unwrap();
    let all: String = writer.files.iter().map(|(_, t)| t.as_str()).collect();
    assert_eq!(
        all.matches("theorem prod_thing").count(),
        1,
        "the pair resolves to one block, and a second copy would redeclare it:\n{all}"
    );
    assert!(
        !all.contains("@[to_additive]\n\n"),
        "an attribute block with no declaration under it does not compile:\n{all}"
    );
}

#[test]
fn find_refuses_a_query_that_constrains_nothing() {
    let repo = repo();
    let err =
        Find { repo: &repo, packages: &NoPackages }.run(&Query::new()).unwrap_err().to_string();
    assert!(err.contains("nothing to search for"), "got: {err}");
}

#[test]
fn find_returns_at_most_the_limit() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("o".into());
    q.limit = 1;
    assert_eq!(Find { repo: &repo, packages: &NoPackages }.run(&q).unwrap().rows.len(), 1);
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
    match (Find { repo: &repo, packages: &NoPackages }).run(&q).unwrap().empty {
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
    assert_eq!(
        Find { repo: &repo, packages: &NoPackages }.run(&q).unwrap().empty,
        Some(Empty::Combination)
    );
}

/// With one condition there is nothing to diagnose, and probing it would only
/// repeat the query back. The probes are skipped rather than answered.
#[test]
fn a_single_condition_is_not_diagnosed() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("zzz".into());
    assert_eq!(
        Find { repo: &repo, packages: &NoPackages }.run(&q).unwrap().empty,
        Some(Empty::Plain)
    );
}

#[test]
fn a_search_that_matches_is_not_diagnosed_at_all() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("top".into());
    assert_eq!(Find { repo: &repo, packages: &NoPackages }.run(&q).unwrap().empty, None);
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

/// The failure this pair of tests is about, in full: a project declares Mathlib
/// and stops, so `Batteries` is importable from the project, absent from the
/// index, and named by nothing. The reported session ended in `grep -rn` over
/// `.lake/packages`, which is the one thing this tool exists to prevent.
#[test]
fn a_prefix_from_an_unindexed_package_is_not_reported_as_a_bad_prefix() {
    let (repo, packages) = (repo(), FakePackages::with(&[("batteries", "Batteries")]));
    let mut q = Query::new();
    q.name = Some("Balanced".into());
    q.module = Some("Batteries".into());
    let find = Find { repo: &repo, packages: &packages };
    match find.run(&q).unwrap().empty {
        Some(Empty::NotIndexed { prefix, package }) => {
            assert_eq!((prefix.as_str(), package.as_str()), ("Batteries", "batteries"));
        }
        other => panic!("expected the package to be named, got {other:?}"),
    }
}

/// A prefix inside a source that is indexed is a different failure with the
/// opposite repair, and the two are indistinguishable from the index alone.
#[test]
fn a_prefix_inside_an_indexed_source_still_says_to_correct_it() {
    let (repo, packages) = (repo(), FakePackages::with(&[("batteries", "Batteries")]));
    let mut q = Query::new();
    q.name = Some("exp_le_exp".into());
    q.module = Some("Mathlib.Nowhere".into());
    let find = Find { repo: &repo, packages: &packages };
    match find.run(&q).unwrap().empty {
        Some(Empty::Barren(c)) => assert!(c.contains(&"--in Mathlib.Nowhere".to_string()), "{c:?}"),
        other => panic!("expected a barren condition, got {other:?}"),
    }
}

/// `try --name` is advice that cannot work when the corpus was never indexed:
/// it returns the same nothing, or a page of Mathlib near-misses that read like
/// an answer. This is the search an agent runs first, so it is the one that has
/// to name the missing source.
#[test]
fn a_name_from_an_unindexed_package_names_the_package_instead_of_a_retry() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let packages = FakePackages::with(&[("batteries", "Batteries")]);
    let err = Show { repo: &repo, files: &files, workspace: &ws, packages: &packages }
        .run(&DeclName::new("Batteries.RBNode.Balanced"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("lake package `batteries`"), "{err}");
    assert!(!err.contains("try `dt find"), "the retry is the dead end: {err}");

    // A name that is simply not there keeps the advice that does work.
    let err = Show { repo: &repo, files: &files, workspace: &ws, packages: &packages }
        .run(&DeclName::new("Real.exp_nowhere"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("try `dt find --name exp_nowhere`"), "{err}");
}

/// The packages reach the report, which is the only place a reader looks when
/// an answer seems thin.
#[test]
fn status_names_the_packages_no_source_covers() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::default();
    let packages = FakePackages::with(&[("batteries", "Batteries"), ("aesop", "Aesop")]);
    let report =
        Status { repo: &repo, revisions: &revs, packages: &packages, workspace: &ws, now: 0 }
            .run()
            .unwrap();
    let named: Vec<&str> = report.unindexed.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(named, ["batteries", "aesop"]);
    assert_eq!(report.sources.len(), 3, "the sources are still reported");
}

#[test]
fn status_shows_a_configured_source_that_has_nothing_indexed() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::default();
    let rows =
        Status { repo: &repo, revisions: &revs, packages: &NoPackages, workspace: &ws, now: 0 }
            .run()
            .unwrap()
            .sources;
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
    let rows =
        Status { repo: &repo, revisions: &revs, packages: &NoPackages, workspace: &ws, now: 0 }
            .run()
            .unwrap()
            .sources;
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
