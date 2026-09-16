//! The use cases against test doubles for every port. What is checked here is
//! the behaviour the plan names: the import line `dt show` prints, the
//! importable frontier that makes `dt add` finite, and the refusal to present
//! guessed dependencies as exact ones.

mod support;

use discrtree::application::add::Add;
use discrtree::application::deps::{Deps, DepsResult};
use discrtree::application::find::{Asked, Dup, Empty, Find};
use discrtree::application::ports::{Missing, NoBuild, Workspace};
use discrtree::application::show::{Show, Source};
use discrtree::application::status::Status;
use discrtree::domain::decl::Span;
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use std::path::PathBuf;
use support::{FakeBuild, FakeFiles, FakeRepo, FakeRevisions, FakeWriter, sources, theorem};

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
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
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
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
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
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
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
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
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
fn show_prints_the_source_of_a_declaration_whose_command_it_does_not_know() {
    // Lean's range is right and the list of headers is not exhaustive:
    // `irreducible_def` is Mathlib's own command, and the lines it points at
    // are the declaration. Calling them a docstring and printing the type
    // instead loses the only source there is.
    let mut d = theorem("MeasureTheory.integral", "mathlib", "Mathlib.Bochner", "G", &[]);
    d.span = Some(Span::new(1, 3));
    let repo = FakeRepo { decls: vec![d] };
    let files = FakeFiles::new().with(
        "mathlib",
        "Mathlib.Bochner",
        "/-- The Bochner integral -/\nirreducible_def integral (\u{3bc} : Measure \u{3b1}) : G :=\n  if hG : CompleteSpace G then \u{2026} else 0\n",
    );
    let ws = workspace();
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
        .run(&DeclName::new("MeasureTheory.integral"))
        .unwrap();
    let Source::Text(t) = &shown.source else {
        panic!("the range is the declaration: {:?}", shown.source)
    };
    assert!(t.contains("irreducible_def integral"), "the source, docstring and all: {t}");
}

#[test]
fn show_offers_no_import_for_a_source_that_cannot_be_imported() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let shown = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
        .run(&DeclName::new("FLT.guessed"))
        .unwrap();
    assert!(shown.import.is_none(), "a text corpus is not on the import path");
}

/// `AddSubgroup.inertia_mono` is in Mathlib and, read as text, in FLT, as
/// `Real.exp_le_exp` is here. The compiled row answers unless a source is asked
/// for, and a source without the name says which sources have it.
#[test]
fn show_from_a_source_takes_the_row_that_source_has() {
    let mut repo = repo();
    let mut copy = theorem("Real.exp_le_exp", "flt", "FLT.Basic", "Eq", &[]);
    copy.elaborated = false;
    repo.decls.insert(0, copy);
    let (files, ws) = (files(), workspace());
    let show = |name: &str, only_in: Option<&SourceId>| {
        Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in }
            .run(&DeclName::new(name))
    };

    assert_eq!(show("Real.exp_le_exp", None).unwrap().decl.source, SourceId::new("mathlib"));
    let flt = SourceId::new("flt");
    let shown = show("Real.exp_le_exp", Some(&flt)).unwrap();
    assert_eq!(shown.decl.source, flt);
    assert!(shown.import.is_none(), "the import is that row's too");

    let err = show("Real.exp_le_exp", Some(&SourceId::new("other"))).unwrap_err().to_string();
    assert_eq!(err, "Real.exp_le_exp is in `flt`, `mathlib`, not in `other`");
    let err = show("No.such", Some(&flt)).unwrap_err().to_string();
    assert!(err.contains("not in the index"), "a name no source has is not a wrong source: {err}");
}

#[test]
fn show_says_which_name_it_could_not_find() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let err = Show { repo: &repo, files: &files, workspace: &ws, build: &NoBuild, only_in: None }
        .run(&DeclName::new("No.such"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("No.such") && err.contains("dt find"), "got: {err}");
}

#[test]
fn deps_lists_one_level_at_a_time() {
    let (repo, ws) = (repo(), workspace());
    let result = Deps { repo: &repo, workspace: &ws, build: &NoBuild }
        .run(&DeclName::new("Other.top"), Some(2))
        .unwrap();
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
    let result = Deps { repo: &repo, workspace: &ws, build: &NoBuild }
        .run(&DeclName::new("FLT.guessed"), Some(1))
        .unwrap();
    match result {
        DepsResult::Levels { approximate, .. } => assert!(approximate),
        _ => panic!("asked for levels"),
    }
}

#[test]
fn deps_with_no_depth_reports_the_size_rather_than_the_contents() {
    let (repo, ws) = (repo(), workspace());
    match (Deps { repo: &repo, workspace: &ws, build: &NoBuild })
        .run(&DeclName::new("Other.top"), None)
        .unwrap()
    {
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
    let err = Find { repo: &repo, build: &NoBuild }.run(&Query::new()).unwrap_err().to_string();
    assert!(err.contains("nothing to search for"), "got: {err}");
}

#[test]
fn find_returns_at_most_the_limit() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("o".into());
    q.limit = 1;
    assert_eq!(Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().rows.len(), 1);
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
    match (Find { repo: &repo, build: &NoBuild }).run(&q).unwrap().empty {
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
    let Some(Empty::Combination { elsewhere }) =
        Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty
    else {
        panic!("both conditions match on their own")
    };
    // "Drop one" on its own leaves the reader to guess which; the module the
    // name does live in is the answer they were after.
    assert_eq!(
        elsewhere.iter().map(|(m, n)| (m.to_string(), *n)).collect::<Vec<_>>(),
        vec![("Other.Main".to_string(), 1)]
    );
}

/// `Real.inner_apply` in miniature: the row's conclusion is `Eq`, one of its
/// argument heads is `Inner.inner`, and the type Lean printed for it says
/// `inner`. That is what a reader copies back into a pattern.
fn exported() -> FakeRepo {
    let mut repo = repo();
    let mut apply = theorem("Real.inner_apply", "mathlib", "Mathlib.Analysis.Inner", "Eq", &[]);
    apply.ty = "∀ (x y : ℝ), inner ℝ x y = x * y".into();
    apply.shape = discrtree::domain::decl::Shape::new(
        Some(DeclName::new("Eq")),
        vec![
            discrtree::domain::decl::ArgHead::Named(DeclName::new("Inner.inner")),
            discrtree::domain::decl::ArgHead::Named(DeclName::new("HMul.hMul")),
        ],
    );
    repo.decls.push(apply);
    // A second constant with the same last component, so the answer has to be
    // chosen rather than found: `Inner.inner` heads the row above and this one
    // heads nothing, which is the whole difference between them.
    let mut other = theorem("Std.HashMap.inner", "mathlib", "Std.HashMap", "Eq", &[]);
    other.shape = discrtree::domain::decl::Shape::new(Some(DeclName::new("Eq")), Vec::new());
    repo.decls.push(other);
    repo
}

/// `export Inner (inner)` makes the pretty-printer drop the namespace, so the
/// pattern a reader writes from a goal is `inner _ _ = _` and the index holds
/// `Inner.inner`. Correcting that by hand is a round trip spent on a word that
/// is not misspelled.
#[test]
fn a_pattern_word_lean_prints_without_its_namespace_still_finds_the_row() {
    let repo = exported();
    let mut q = Query::new();
    q.shape = discrtree::domain::decl::Shape::new(
        Some(DeclName::new("Eq")),
        vec![discrtree::domain::decl::ArgHead::Named(DeclName::new("inner"))],
    );
    let hits = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap();
    assert_eq!(hits.rows.len(), 1, "{:?}", hits.rows);
    assert_eq!(hits.rows[0].name.as_str(), "Real.inner_apply");
    // And says so: the rows answer a question spelled differently from the
    // one that was asked.
    assert_eq!(hits.read_as, vec![("inner".to_string(), DeclName::new("Inner.inner"))]);
}

/// The word is resolved and the search still fails -- `Inner.inner` heads no
/// conclusion. "matches nothing on its own" would send the reader to correct a
/// word that is spelled exactly as Lean prints it.
#[test]
fn a_word_that_resolves_to_a_constant_that_answers_nothing_names_the_constant() {
    let repo = exported();
    let mut q = Query::new();
    q.shape = discrtree::domain::decl::Shape::new(Some(DeclName::new("inner")), vec![]);
    match (Find { repo: &repo, build: &NoBuild }).run(&q).unwrap().empty {
        Some(Empty::Unqualified { written, candidates }) => {
            assert_eq!(written, "inner");
            assert_eq!(candidates.first().map(|c| c.as_str()), Some("Inner.inner"));
        }
        other => panic!("expected the word to be resolved, got {other:?}"),
    }
}

/// An index whose text rows are the only ones marked `instance`.
fn with_instances(elaborated_too: bool) -> FakeRepo {
    let mut repo = repo();
    let mut scanned = theorem("Heis.instMul", "flt", "FLT.Basic", "Mul", &[]);
    scanned.kind = discrtree::domain::decl::DeclKind::Instance;
    scanned.elaborated = false;
    repo.decls.push(scanned);
    if elaborated_too {
        let mut dumped =
            theorem("Real.instTopologicalSpace", "mathlib", "Mathlib.Analysis.Exp", "T", &[]);
        dumped.kind = discrtree::domain::decl::DeclKind::Instance;
        repo.decls.push(dumped);
    }
    repo
}

/// A pattern is several conditions inside -- one conclusion head and one
/// argument head each -- and one thing to whoever wrote it. `Real.log _ ≤
/// Real.sqrt _` was answered "every condition matches on its own; drop one",
/// and there is no flag there to drop. What is worth saying about a shape
/// nothing has is which nearby shape something does.
#[test]
fn a_pattern_that_matches_nothing_is_answered_about_the_pattern() {
    use discrtree::domain::decl::{ArgHead, Shape};
    let shaped = |name: &str, concl: &str, args: &[&str]| {
        let mut d = theorem(name, "mathlib", "Mathlib.Analysis.Exp", concl, &[]);
        d.shape = Shape::new(
            Some(DeclName::new(concl)),
            args.iter().map(|a| ArgHead::parse(a)).collect(),
        );
        d
    };
    // `≤` carries two leading type and instance arguments, as it does in the
    // index; the alignment search is what gets past them.
    let mut repo = FakeRepo {
        decls: vec![
            shaped("Real.log_le_self", "LE.le", &["_", "_", "Real.log", "_"]),
            shaped("Real.le_sqrt", "LE.le", &["_", "_", "_", "Real.sqrt"]),
            shaped("Real.log_eq_sqrt", "Eq", &["_", "Real.log", "Real.sqrt"]),
        ],
    };
    let mut q = Query::new();
    q.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![ArgHead::parse("Real.log"), ArgHead::parse("Real.sqrt")],
    );

    let found = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty;
    let Some(Empty::NoSuchShape { under, without, swapped }) = found else {
        panic!("expected the shape to be diagnosed, got {found:?}")
    };
    assert!(!swapped, "nothing has these two under `LE.le` either way round");
    assert_eq!(under, vec![(DeclName::new("Eq"), 1)], "the wrong relation, the right sides");
    assert_eq!(
        without,
        vec![DeclName::new("Real.log"), DeclName::new("Real.sqrt")],
        "either side matches without the other"
    );

    // And when the index has the two sides the other way round, that is the
    // whole of the answer: one character to fix rather than a search to redo.
    repo.decls.push(shaped("Real.sqrt_le_log", "LE.le", &["_", "_", "Real.sqrt", "Real.log"]));
    let found = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty;
    assert!(matches!(found, Some(Empty::NoSuchShape { swapped: true, .. })), "got {found:?}");
}

/// A pattern that fails *with* a flag is still a combination: the flag is
/// there to be dropped, and the shape is not what is wrong.
#[test]
fn a_pattern_that_matches_on_its_own_is_still_blamed_on_the_combination() {
    let repo = repo();
    let mut q = Query::new();
    q.shape = discrtree::domain::decl::Shape::new(Some(DeclName::new("LE.le")), Vec::new());
    q.module = Some("Other".into());
    let found = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty;
    assert!(matches!(found, Some(Empty::Combination { .. })), "got {found:?}");
}

/// Lean has no `instance` constant: an instance is a `def` with an attribute,
/// and a dump that read only the constructor recorded every one of them as
/// `def`. `--kind instance` then selected the text-scanned rows and nothing
/// else -- and "drop a condition" is the one repair that cannot help, because
/// the flag is right and the index is old.
#[test]
fn asking_for_an_instance_where_the_dump_recorded_none_says_the_dump_is_old() {
    let repo = with_instances(false);
    let mut q = Query::new();
    q.kind = vec![discrtree::domain::decl::DeclKind::Instance];
    q.module = Some("Mathlib.Analysis.Exp".into());
    assert_eq!(
        Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty,
        Some(Empty::InstancesAreDefs)
    );
}

/// And once a source has been read again, the same query is diagnosed like
/// any other: the kind is in the index, so the combination is what failed.
#[test]
fn an_index_that_has_instances_diagnoses_them_like_any_other_kind() {
    let repo = with_instances(true);
    let mut q = Query::new();
    q.kind = vec![discrtree::domain::decl::DeclKind::Instance];
    q.module = Some("Other.Main".into());
    assert!(matches!(
        Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty,
        Some(Empty::Combination { .. })
    ));
}

/// An empty search names no sources, so the staleness warning it carries falls
/// back to every source in the workspace -- a line about the project on the end
/// of every failed Mathlib search, after every `lake build`. A query that says
/// where it is looking can be taken at its word.
#[test]
fn a_query_that_names_where_it_looks_is_answerable_only_from_there() {
    let repo = repo();
    let mut q = Query::new();
    q.module = Some("Mathlib.Analysis".into());
    assert_eq!(
        discrtree::application::find::sources_of(&repo, &q),
        std::collections::BTreeSet::from([SourceId::new("mathlib")]),
        "the index resolves a module prefix to the source that holds it"
    );

    let mut named = Query::new();
    named.source = Some(SourceId::new("flt"));
    assert_eq!(
        discrtree::application::find::sources_of(&repo, &named),
        std::collections::BTreeSet::from([SourceId::new("flt")]),
        "--source says it outright, with no query at all"
    );

    // A prefix nothing is indexed under says nothing about where the answer
    // would have been: an empty set is "anywhere", which is what the caller
    // reads it as.
    let mut nowhere = Query::new();
    nowhere.module = Some("Nowhere".into());
    assert!(discrtree::application::find::sources_of(&repo, &nowhere).is_empty());
    assert!(discrtree::application::find::sources_of(&repo, &Query::new()).is_empty());
}

/// With one condition there is nothing to diagnose, and probing it would only
/// repeat the query back. The probes are skipped rather than answered.
#[test]
fn a_single_condition_is_not_diagnosed() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("zzz".into());
    assert_eq!(Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty, Some(Empty::Plain));
}

#[test]
fn a_search_that_matches_is_not_diagnosed_at_all() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("top".into());
    assert_eq!(Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty, None);
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
    let (repo, build) = (repo(), FakeBuild::with(&[("batteries", "Batteries")]));
    let mut q = Query::new();
    q.name = Some("Balanced".into());
    q.module = Some("Batteries".into());
    let find = Find { repo: &repo, build: &build };
    match find.run(&q).unwrap().empty {
        Some(Empty::NotIndexed { asked, missing: Missing::Package(pkg) }) => {
            assert_eq!((asked.as_str(), pkg.as_str()), ("Batteries", "batteries"));
        }
        other => panic!("expected the package to be named, got {other:?}"),
    }
}

/// A prefix inside a source that is indexed is a different failure with the
/// opposite repair, and the two are indistinguishable from the index alone.
#[test]
fn a_prefix_inside_an_indexed_source_still_says_to_correct_it() {
    let (repo, build) = (repo(), FakeBuild::with(&[("batteries", "Batteries")]));
    let mut q = Query::new();
    q.name = Some("exp_le_exp".into());
    q.module = Some("Mathlib.Nowhere".into());
    let find = Find { repo: &repo, build: &build };
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
    let build = FakeBuild::with(&[("batteries", "Batteries")]);
    let err = Show { repo: &repo, files: &files, workspace: &ws, build: &build, only_in: None }
        .run(&DeclName::new("Batteries.RBNode.Balanced"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("lake package `batteries`"), "{err}");
    assert!(!err.contains("try `dt find"), "the retry is the dead end: {err}");

    // A name that is simply not there keeps the advice that does work.
    let err = Show { repo: &repo, files: &files, workspace: &ws, build: &build, only_in: None }
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
    let build = FakeBuild::with(&[("batteries", "Batteries"), ("aesop", "Aesop")]);
    let report = Status { repo: &repo, revisions: &revs, build: &build, workspace: &ws, now: 0 }
        .run()
        .unwrap();
    let named: Vec<&str> = report.unindexed.iter().map(|p| p.name.as_str()).collect();
    assert_eq!(named, ["batteries", "aesop"]);
    assert_eq!(report.sources.len(), 3, "the sources are still reported");
}

/// Core is the same failure as an unindexed package, one level down, and the
/// package repair does not reach it: `Int.add_one_le_iff` is proved in
/// `Init/Data/Int/Order.lean`, core is no lake package, and `--name
/// add_one_le_iff` answers with ten `PNat`, `ENat` and `Cardinal` namesakes
/// that read like a complete answer to a question it never searched.
#[test]
fn a_name_from_lean_core_says_so_rather_than_sending_the_reader_to_name_search() {
    let (repo, files, ws) = (repo(), files(), workspace());
    let build = FakeBuild::with(&[]).without_core();
    let err = Show { repo: &repo, files: &files, workspace: &ws, build: &build, only_in: None }
        .run(&DeclName::new("Int.add_one_le_iff"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("Lean core"), "{err}");
    assert!(err.contains("`Int`"), "the namespace that is core's, not the whole name: {err}");
    assert!(!err.contains("try `dt find"), "the retry cannot reach a corpus nobody dumped: {err}");

    // And a namespace core does not own keeps the advice that works. The list
    // is narrow on purpose: an explanation that fits every missing name
    // explains nothing.
    let err = Show { repo: &repo, files: &files, workspace: &ws, build: &build, only_in: None }
        .run(&DeclName::new("Real.exp_nowhere"))
        .unwrap_err()
        .to_string();
    assert!(err.contains("try `dt find --name exp_nowhere`"), "{err}");
}

/// The module roots and the namespaces are different lists, and `--in` is asked
/// with the first: `Int.add_one_le_iff` lives in `Init.Data.Int.Order`.
#[test]
fn a_module_prefix_from_lean_core_names_core_and_not_a_bad_prefix() {
    let (repo, build) = (repo(), FakeBuild::with(&[]).without_core());
    let mut q = Query::new();
    q.name = Some("add_one_le_iff".into());
    q.module = Some("Init.Data.Int".into());
    let find = Find { repo: &repo, build: &build };
    match find.run(&q).unwrap().empty {
        Some(Empty::NotIndexed { asked: Asked::Module(prefix), missing: Missing::Core(tc) }) => {
            assert_eq!(prefix, "Init.Data.Int");
            assert_eq!(tc, "leanprover/lean4:v4.33.1");
        }
        other => panic!("expected core to be named, got {other:?}"),
    }
}

/// The note has to reach every command that can be handed a qualified name,
/// not only the one it was written in. `dt show` sends the reader to
/// `dt find --name`, and a bare `no match` there argues them straight back out
/// of what they were just told.
#[test]
fn a_qualified_name_search_from_an_unindexed_corpus_says_so() {
    let (repo, build) = (repo(), FakeBuild::with(&[]).without_core());
    let mut q = Query::new();
    q.name = Some("Int.emod_emod_of_dvd".into());
    let find = Find { repo: &repo, build: &build };
    match find.run(&q).unwrap().empty {
        Some(Empty::NotIndexed { asked: Asked::Name(n), missing: Missing::Core(_) }) => {
            assert_eq!(n.namespace_root(), "Int");
        }
        other => panic!("expected core to be named, got {other:?}"),
    }

    // An unqualified fragment has no namespace to read, and guessing one from
    // a substring would be inventing the evidence. `--name` takes fragments
    // most of the time, so this is the common case and it stays quiet.
    let mut q = Query::new();
    q.name = Some("emod_emod_of_dvd".into());
    assert_eq!(find.run(&q).unwrap().empty, Some(Empty::Plain));

    // And a name whose namespace is indexed keeps the plain answer.
    let mut q = Query::new();
    q.name = Some("Real.exp_nowhere".into());
    assert_eq!(find.run(&q).unwrap().empty, Some(Empty::Plain));
}

/// The third entry point, and the one a reader reaches already holding a fully
/// qualified name they read somewhere else.
#[test]
fn deps_on_a_name_from_an_unindexed_corpus_names_the_corpus() {
    let (repo, ws) = (repo(), workspace());
    let build = FakeBuild::with(&[("batteries", "Batteries")]).without_core();
    let fails = |n: &str| match (Deps { repo: &repo, workspace: &ws, build: &build })
        .run(&DeclName::new(n), Some(1))
    {
        Err(e) => e.to_string(),
        Ok(_) => panic!("{n} is not in this index"),
    };
    let err = fails("Int.add_one_le_iff");
    assert!(err.contains("Lean core"), "{err}");

    let err = fails("Batteries.RBNode.Balanced");
    assert!(err.contains("lake package `batteries`"), "{err}");

    // Nothing to blame, nothing added: the message is the one it always was.
    let err = fails("Real.exp_nowhere");
    assert_eq!(err, "Real.exp_nowhere is not in the index");
}

/// Where a reader looks when an answer seems thin, and the one corpus that
/// cannot appear in the table above it: nothing was ever dumped to count.
#[test]
fn status_names_the_toolchain_whose_core_is_not_indexed() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::default();
    let build = FakeBuild::with(&[]).without_core();
    let report = Status { repo: &repo, revisions: &revs, build: &build, workspace: &ws, now: 0 }
        .run()
        .unwrap();
    let tc = report.toolchain.expect("the toolchain reaches the report");
    assert_eq!(tc.name, "leanprover/lean4:v4.33.1");
    assert!(!tc.indexed);
}

#[test]
fn status_shows_a_configured_source_that_has_nothing_indexed() {
    let (repo, ws) = (repo(), workspace());
    let revs = FakeRevisions::default();
    let rows = Status { repo: &repo, revisions: &revs, build: &NoBuild, workspace: &ws, now: 0 }
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
    let rows = Status { repo: &repo, revisions: &revs, build: &NoBuild, workspace: &ws, now: 0 }
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

/// `dt find --name Real.exp` and `dt show Real.exp` should agree about which
/// declaration is meant. The filter is a substring and the rows that extend
/// the name outnumber it, so without a ranking rule the row that was named
/// arrives below them -- and below the default limit, on a real corpus.
#[test]
fn asking_for_a_declaration_by_its_whole_name_puts_it_first() {
    let repo = repo();
    let mut q = Query::new();
    q.name = Some("Real.exp".into());
    let hits = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap();
    assert_eq!(hits.rows.first().map(|d| d.name.as_str()), Some("Real.exp"), "{:?}", hits.rows);
    // Unqualified, the row called that is still the one meant: `Real.exp` is
    // what `exp` names here, and `Real.exp_le_exp` is not.
    q.name = Some("exp".into());
    let hits = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap();
    assert_eq!(hits.rows.first().map(|d| d.name.as_str()), Some("Real.exp"), "{:?}", hits.rows);
}

fn shaped_as(
    name: &str,
    module: &str,
    concl: &str,
    args: &[&str],
    consts: &[&str],
) -> discrtree::domain::decl::Decl {
    use discrtree::domain::decl::{ArgHead, Shape};
    let mut d = theorem(name, "mathlib", module, concl, consts);
    d.shape =
        Shape::new(Some(DeclName::new(concl)), args.iter().map(|a| ArgHead::parse(a)).collect());
    d
}

/// A name inside a pattern is one condition to whoever wrote it, and "matches
/// nothing on its own" is not true of it: the shape matches, and so does the
/// name, only never in the same statement.
#[test]
fn a_constant_the_shape_never_mentions_is_named_as_such() {
    use discrtree::domain::decl::{ArgHead, Shape};
    let repo = FakeRepo {
        decls: vec![
            shaped_as("List.a", "M", "Eq", &["_", "HAppend.hAppend", "_"], &["List.take"]),
            shaped_as("List.b", "M", "Eq", &["_", "HAppend.hAppend", "_"], &["List.drop"]),
            shaped_as("List.c", "M", "LE.le", &["_", "_"], &["List.take", "List.drop"]),
        ],
    };
    let pattern = |uses: &[&str]| {
        let mut q = Query::new();
        q.shape = Shape::new(
            Some(DeclName::new("Eq")),
            vec![ArgHead::parse("HAppend.hAppend"), ArgHead::Any],
        );
        q.uses = uses.iter().map(|u| DeclName::new(*u)).collect();
        q.pattern_uses = q.uses.clone();
        q
    };

    let found = Find { repo: &repo, build: &NoBuild }.run(&pattern(&["List.length"])).unwrap();
    assert!(matches!(found.empty, Some(Empty::Barren(_))), "absent everywhere: {:?}", found.empty);

    // Each of the two sits under this shape somewhere; never both.
    let found = Find { repo: &repo, build: &NoBuild }.run(&pattern(&["List.take", "List.drop"]));
    let Some(Empty::NotInShape { absent, together }) = found.unwrap().empty else {
        panic!("expected the pattern's constants to be blamed")
    };
    assert!(together);
    assert_eq!(absent, vec![DeclName::new("List.take"), DeclName::new("List.drop")]);

    let mut repo = repo;
    repo.decls.remove(1);
    let found = Find { repo: &repo, build: &NoBuild }.run(&pattern(&["List.take", "List.drop"]));
    assert_eq!(
        found.unwrap().empty,
        Some(Empty::NotInShape { absent: vec![DeclName::new("List.drop")], together: false })
    );
}

/// `--name sublist_cons_iff` with the pattern `List.Sublist _ _` found
/// nothing, and the lemma was there: it concludes an `Iff` with the sublist
/// on one side. The name is exact, so what the reader got wrong is the shape.
#[test]
fn a_named_declaration_of_another_shape_is_shown_with_its_shape() {
    use discrtree::domain::decl::{ArgHead, Shape};
    let repo = FakeRepo {
        decls: vec![
            shaped_as("List.sublist_cons_iff", "M", "Iff", &["List.Sublist", "Or"], &[]),
            shaped_as("List.Sublist.refl", "M", "List.Sublist", &["_", "_"], &[]),
        ],
    };
    let mut q = Query::new();
    q.name = Some("sublist_cons_iff".into());
    q.shape = Shape::new(Some(DeclName::new("List.Sublist")), vec![ArgHead::Any, ArgHead::Any]);
    let found = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty;
    let Some(Empty::NamedElsewise { name, shape, on_a_side }) = found else {
        panic!("expected the named declaration, got {found:?}")
    };
    assert_eq!(name, DeclName::new("List.sublist_cons_iff"));
    assert_eq!(shape.concl, Some(DeclName::new("Iff")));
    assert!(on_a_side, "the pattern is one side of that `Iff`");

    // A fragment of a name is a search, not a declaration to point at.
    q.name = Some("sublist_cons".into());
    let found = Find { repo: &repo, build: &NoBuild }.run(&q).unwrap().empty;
    assert!(!matches!(found, Some(Empty::NamedElsewise { .. })), "got {found:?}");
}

/// `ctorIdx` and `congr_simp` outnumbered the lemmas of a small module. They
/// are hidden, and a search only they answer says so instead of "no match".
#[test]
fn a_search_only_generated_names_answer_says_they_are_hidden() {
    let mut elim = theorem("Form.and.elim", "mathlib", "M", "Eq", &[]);
    elim.ty = "(t : Form) → t.ctorIdx = 3 → motive t".into();
    let repo = FakeRepo {
        decls: vec![
            theorem("Form.ctorIdx", "mathlib", "M", "Eq", &[]),
            elim,
            theorem("Or.elim", "mathlib", "M", "Eq", &[]),
        ],
    };
    let named = |n: &str| {
        let mut q = Query::new();
        q.name = Some(n.into());
        q
    };
    let run = |q: &Query| Find { repo: &repo, build: &NoBuild }.run(q).unwrap();

    assert!(run(&named("ctorIdx")).rows.is_empty());
    assert_eq!(run(&named("ctorIdx")).empty, Some(Empty::OnlyGenerated));
    assert_eq!(run(&named("Form.and.elim")).empty, Some(Empty::OnlyGenerated));
    assert_eq!(run(&named("elim")).rows.len(), 1, "`Or.elim` is written by hand");
    let mut shown = named("ctorIdx");
    shown.generated = true;
    assert_eq!(run(&shown).rows.len(), 1);
}

/// `dt rdeps` reads proofs as well as statements, which is what `--uses`
/// could not, and says which of the two each mention is.
#[test]
fn rdeps_lists_what_mentions_a_declaration_in_a_proof_or_a_statement() {
    use discrtree::application::rdeps::Rdeps;
    let mut in_proof = theorem("B.proof", "mathlib", "Mathlib.B", "Eq", &["X.root"]);
    in_proof.consts.clear();
    let mut recursive = theorem("X.root", "mathlib", "Mathlib.X", "Eq", &["X.root"]);
    recursive.consts.clear();
    let repo = FakeRepo {
        decls: vec![
            recursive,
            theorem("A.stated", "mathlib", "Mathlib.A", "Eq", &["X.root"]),
            in_proof,
            theorem("C.unrelated", "mathlib", "Mathlib.A", "Eq", &["Y"]),
        ],
    };
    let rdeps = Rdeps { repo: &repo, build: &NoBuild };
    let root = DeclName::new("X.root");

    let u = rdeps.run(&root, &Query::new()).unwrap();
    assert_eq!(u.total, 2, "itself and the unrelated one are not users");
    let shown: Vec<(&str, bool)> =
        u.shown.iter().map(|m| (m.decl.name.as_str(), m.in_statement)).collect();
    assert_eq!(shown, vec![("A.stated", true), ("B.proof", false)]);

    let mut first = Query::new();
    first.limit = 1;
    let u = rdeps.run(&root, &first).unwrap();
    assert_eq!((u.total, u.shown.len()), (2, 1));

    let mut within = Query::new();
    within.module = Some("Mathlib.B".into());
    assert_eq!(rdeps.run(&root, &within).unwrap().total, 1);

    assert!(rdeps.run(&DeclName::new("Nope"), &Query::new()).is_err());
}
