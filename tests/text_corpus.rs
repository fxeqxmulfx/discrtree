//! The text path end to end: a directory of `.lean` files, read by the real
//! filesystem adapter, scanned without Lean, and indexed.
//!
//! Every row this path produces is `elaborated: false`, and the test says so in
//! as many ways as it can, because the one thing that must never happen is a
//! text row answering a question only an elaborated row can answer.

mod support;

use discrtree::application::index;
use discrtree::application::ports::{DeclRepo, DeclSink, SourceFiles};
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::query::Query;
use discrtree::domain::source::{SourceId, SourceKind, SourceMeta};
use discrtree::infrastructure::project::Files;
use discrtree::infrastructure::sqlite::SqliteIndex;
use std::collections::BTreeMap;
use support::{TempDir, theorem};

const MODULE: &str = r#"import Mathlib.Analysis.Exp
import FLT.Basic

/-- The reverting step of the exact sequence. -/
theorem p2m_exact_reverting (x : ℝ) : Real.exp x > 0 := by
  positivity

def helper (n : ℕ) : ℕ :=
  n + 1

theorem unfinished : False := by
  sorry
"#;

fn corpus() -> (TempDir, Files, SourceMeta) {
    let dir = TempDir::new("corpus");
    dir.write("FLT/Basic.lean", MODULE);
    // Never read, however large: this is what `exclude` is for.
    dir.write("html/Generated.lean", "theorem noise : True := trivial\n");
    dir.write(".git/objects/Packed.lean", "theorem hidden : True := trivial\n");

    let id = SourceId::new("flt");
    let files = Files {
        roots: BTreeMap::from([(id.clone(), dir.path().to_path_buf())]),
        excludes: BTreeMap::from([(id.clone(), vec!["html".to_string()])]),
    };
    let meta = SourceMeta {
        id,
        kind: SourceKind::Git,
        elaborated: false,
        importable: false,
        rev: Some("deadbeef".into()),
        license: Some("Apache-2.0".into()),
        attribution: None,
    };
    (dir, files, meta)
}

#[test]
fn the_walk_skips_excluded_and_dot_directories() {
    let (_dir, files, meta) = corpus();
    let modules: Vec<String> =
        files.list_modules(&meta.id).unwrap().into_iter().map(|(m, _)| m.to_string()).collect();
    assert_eq!(modules, ["FLT.Basic"], "got: {modules:?}");
}

#[test]
fn a_module_is_read_by_its_module_name_not_its_path() {
    let (_dir, files, meta) = corpus();
    let text = files.read_module(&meta.id, &ModuleName::new("FLT.Basic")).unwrap();
    assert!(text.contains("p2m_exact_reverting"));
}

#[test]
fn scanning_finds_the_declarations_with_their_kinds_and_ranges() {
    let (_dir, files, meta) = corpus();
    let decls = index::scan_source(&meta, &files, None).unwrap().decls;
    let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
    assert_eq!(names, ["p2m_exact_reverting", "helper", "unfinished"], "got: {names:?}");

    let thm = &decls[0];
    assert_eq!(thm.kind.as_str(), "theorem");
    assert_eq!(thm.doc.as_deref(), Some("The reverting step of the exact sequence."));
    assert!(thm.ty.contains("Real.exp x > 0"), "got: {}", thm.ty);
    let span = thm.span.expect("a scanned declaration has a line range");
    assert_eq!(
        MODULE.lines().nth(span.start as usize - 1).unwrap().trim_start(),
        "theorem p2m_exact_reverting (x : \u{211d}) : Real.exp x > 0 := by"
    );
}

#[test]
fn a_declaration_proved_by_sorry_is_flagged() {
    let (_dir, files, meta) = corpus();
    let decls = index::scan_source(&meta, &files, None).unwrap().decls;
    let unfinished = decls.iter().find(|d| d.name.as_str() == "unfinished").unwrap();
    assert!(unfinished.has_sorry);
    assert!(!decls[0].has_sorry);
}

#[test]
fn every_scanned_row_is_marked_as_not_elaborated_and_carries_no_shape() {
    let (_dir, files, meta) = corpus();
    for d in index::scan_source(&meta, &files, None).unwrap().decls {
        assert!(!d.elaborated, "{} came from a scanner, not from Lean", d.name);
        assert!(
            !d.shaped(),
            "{}: a shape here would let it answer a shape query it cannot answer",
            d.name
        );
    }
}

#[test]
fn a_scanned_dependency_is_kept_only_when_the_index_knows_the_name() {
    let (_dir, files, meta) = corpus();

    // With nothing indexed there is nothing to resolve against, so no
    // identifier is promoted to a dependency.
    let blind = index::scan_source(&meta, &files, None).unwrap().decls;
    assert!(blind[0].deps.is_empty());

    let mut db = SqliteIndex::in_memory().unwrap();
    index::load(&mut db, &[theorem("Real.exp", "mathlib", "Mathlib.Analysis.Exp", "Real", &[])])
        .unwrap();
    db.finish().unwrap();

    let resolved = index::scan_source(&meta, &files, Some(&db)).unwrap().decls;
    assert_eq!(resolved[0].deps, vec![DeclName::new("Real.exp")]);
}

#[test]
fn a_text_corpus_is_searchable_by_name_and_text_but_not_by_shape() {
    let (_dir, files, meta) = corpus();
    let mut db = SqliteIndex::in_memory().unwrap();
    let decls = index::scan_source(&meta, &files, None).unwrap().decls;
    index::load(&mut db, &decls).unwrap();
    db.finish().unwrap();

    let mut q = Query::new();
    q.name = Some("p2m".into());
    assert_eq!(db.find(&q).unwrap().len(), 1);

    let mut q = Query::new();
    q.shape.concl = Some(DeclName::new("GT.gt"));
    assert!(
        db.find(&q).unwrap().is_empty(),
        "no scanner reads a conclusion head symbol, so this must find nothing \
         rather than something plausible"
    );
}
