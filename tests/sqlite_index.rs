//! The SQLite adapter against the real engine: rows survive a round trip, the
//! domain's query rule and the SQL agree, and an elaborated row wins over a
//! text row with the same name.

mod support;

use discrtree::application::index;
use discrtree::application::ports::{DeclRepo, DeclSink};
use discrtree::domain::decl::{ArgHead, DeclKind, Shape, Span};
use discrtree::domain::name::DeclName;
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use discrtree::infrastructure::sqlite::SqliteIndex;
use support::{TempDir, theorem};

fn loaded() -> SqliteIndex {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut rows = vec![
        theorem("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Exp", "LE.le", &["Real.exp"]),
        theorem("Real.exp_lt_exp", "mathlib", "Mathlib.Analysis.Exp", "LT.lt", &["Real.exp"]),
        theorem("Finset.sum_le_sum", "mathlib", "Mathlib.Algebra.Order", "LE.le", &["Finset.sum"]),
    ];
    rows[0].ty = "Real.exp x ≤ Real.exp y ↔ x ≤ y".into();
    rows[0].doc = Some("The exponential is monotone.".into());
    rows[0].span = Some(Span::new(316, 318));
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    db
}

#[test]
fn a_row_survives_the_round_trip_through_sqlite() {
    let db = loaded();
    let got = db.get(&DeclName::new("Real.exp_le_exp")).unwrap().unwrap();
    assert_eq!(got.module.as_str(), "Mathlib.Analysis.Exp");
    assert_eq!(got.kind, DeclKind::Theorem);
    assert_eq!(got.ty, "Real.exp x ≤ Real.exp y ↔ x ≤ y");
    assert_eq!(got.shape.concl.as_ref().map(|c| c.as_str()), Some("LE.le"));
    assert_eq!(got.span, Some(Span::new(316, 318)));
    assert!(got.elaborated);
    // The side tables are what make `--uses` an index lookup; a row read back
    // without them would make `dt deps` silently empty.
    assert_eq!(got.deps, vec![DeclName::new("Real.exp")]);
    assert_eq!(got.consts, vec![DeclName::new("Real.exp")]);
}

#[test]
fn the_conclusion_head_narrows_the_search() {
    let db = loaded();
    let mut q = Query::new();
    q.shape = Shape::new(Some(DeclName::new("LE.le")), Vec::new());
    let names: Vec<String> = db.find(&q).unwrap().iter().map(|d| d.name.to_string()).collect();
    assert_eq!(names.len(), 2, "got: {names:?}");
    assert!(!names.contains(&"Real.exp_lt_exp".to_string()));
}

#[test]
fn use_conditions_combine_with_and() {
    let db = loaded();
    let mut q = Query::new();
    q.uses = vec![DeclName::new("Real.exp"), DeclName::new("Finset.sum")];
    assert!(db.find(&q).unwrap().is_empty(), "no declaration mentions both");

    q.uses = vec![DeclName::new("Finset.sum")];
    assert_eq!(db.find(&q).unwrap().len(), 1);
}

#[test]
fn the_module_condition_matches_a_prefix_on_component_boundaries() {
    let db = loaded();
    let mut q = Query::new();
    q.module = Some("Mathlib.Analysis".into());
    assert_eq!(db.find(&q).unwrap().len(), 2);

    // `Mathlib.Analys` is not a prefix of `Mathlib.Analysis.Exp` in the sense
    // that matters, and matching it would make `--in` quietly wrong.
    q.module = Some("Mathlib.Analys".into());
    assert!(db.find(&q).unwrap().is_empty());
}

#[test]
fn argument_shape_is_matched_even_though_sql_cannot_express_it() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut row = theorem("le_of_exp", "mathlib", "M", "LE.le", &[]);
    row.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![
            ArgHead::Named(DeclName::new("Real")),
            ArgHead::Any,
            ArgHead::Named(DeclName::new("Real.exp")),
            ArgHead::Any,
        ],
    );
    index::load(&mut db, &[row]).unwrap();
    db.finish().unwrap();

    // `Real.exp _ ≤ _` has to find it past the type and the instance argument
    // the elaborator inserted, which is what the alignment search is for.
    let mut q = Query::new();
    q.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![ArgHead::Named(DeclName::new("Real.exp")), ArgHead::Any],
    );
    assert_eq!(db.find(&q).unwrap().len(), 1);

    q.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![ArgHead::Named(DeclName::new("Finset.sum")), ArgHead::Any],
    );
    assert!(db.find(&q).unwrap().is_empty());
}

#[test]
fn an_elaborated_row_wins_over_a_text_row_with_the_same_name() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let compiled = theorem("Foo.bar", "mathlib", "Mathlib.Foo", "Eq", &["Nat.add"]);
    let mut text = theorem("Foo.bar", "flt", "FLT.Foo", "Eq", &[]);
    text.elaborated = false;
    text.shape = Shape::default();
    index::load(&mut db, &[text, compiled]).unwrap();
    db.finish().unwrap();

    let got = db.get(&DeclName::new("Foo.bar")).unwrap().unwrap();
    assert!(got.elaborated, "the guessed answer must not shadow the elaborated one");
    assert_eq!(got.source, SourceId::new("mathlib"));
    assert_eq!(db.count().unwrap(), 2, "both rows are kept; they answer different questions");
}

#[test]
fn asking_for_elaborated_rows_excludes_the_text_corpus() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut text = theorem("FLT.thing", "flt", "FLT.Foo", "Eq", &[]);
    text.elaborated = false;
    text.shape = Shape::default();
    index::load(&mut db, &[text, theorem("M.thing", "mathlib", "M", "Eq", &[])]).unwrap();
    db.finish().unwrap();

    let mut q = Query::new();
    q.name = Some("thing".into());
    assert_eq!(db.find(&q).unwrap().len(), 2);
    q.elaborated_only = true;
    assert_eq!(db.find(&q).unwrap().len(), 1);
}

#[test]
fn re_indexing_a_source_replaces_it_rather_than_duplicating_it() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let rows =
        vec![theorem("A", "mathlib", "M", "Eq", &[]), theorem("B", "mathlib", "M", "Eq", &[])];
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    assert_eq!(db.count().unwrap(), 2);

    assert_eq!(db.clear_source(&SourceId::new("mathlib")).unwrap(), 2);
    index::load(&mut db, &rows[..1]).unwrap();
    db.finish().unwrap();
    assert_eq!(db.count().unwrap(), 1);
    // The side tables have to go with them, or `--uses` keeps matching rows
    // that are no longer there.
    let mut q = Query::new();
    q.uses = vec![DeclName::new("Real.exp")];
    assert!(db.find(&q).unwrap().iter().all(|d| d.name.as_str() == "A"));
}

#[test]
fn get_many_answers_in_the_order_asked_because_add_depends_on_it() {
    let db = loaded();
    let names: Vec<DeclName> = ["Finset.sum_le_sum", "Real.exp_le_exp", "Nope.missing"]
        .iter()
        .map(|n| DeclName::new(*n))
        .collect();
    let got = db.get_many(&names).unwrap();
    assert_eq!(
        got.iter().map(|d| d.name.to_string()).collect::<Vec<_>>(),
        vec!["Finset.sum_le_sum", "Real.exp_le_exp"],
        "a missing name is skipped, and the rest keep their topological order"
    );
}

#[test]
fn counts_are_reported_per_source() {
    let db = loaded();
    assert_eq!(db.counts().unwrap(), vec![(SourceId::new("mathlib"), 3)]);
}

#[test]
fn an_index_on_disk_is_reopened_with_its_rows() {
    let dir = TempDir::new("reopen");
    let path = dir.path().join("nested/index.db");
    {
        let mut db = SqliteIndex::open(&path).unwrap();
        index::load(&mut db, &[theorem("A", "mathlib", "M", "Eq", &[])]).unwrap();
        db.finish().unwrap();
    }
    let db = SqliteIndex::open(&path).unwrap();
    assert_eq!(db.count().unwrap(), 1);
    assert!(db.get(&DeclName::new("A")).unwrap().is_some());
}

#[test]
fn a_named_argument_is_found_past_the_over_fetch_cap() {
    // The positional match happens in the domain, so SQLite over-fetches and
    // the domain filters. Before the argument heads were pushed into the
    // query, that made a shape search look only at the first few hundred rows
    // sharing a conclusion — and `LE.le` alone has tens of thousands in
    // Mathlib, so the answer was reliably not among them.
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut rows: Vec<_> = (0..3000)
        .map(|i| {
            let mut d = theorem(&format!("decoy_{i}"), "mathlib", "M", "LE.le", &[]);
            d.shape = Shape::new(
                Some(DeclName::new("LE.le")),
                vec![
                    ArgHead::Named(DeclName::new("Real")),
                    ArgHead::Any,
                    ArgHead::Named(DeclName::new("HAdd.hAdd")),
                    ArgHead::Any,
                ],
            );
            d
        })
        .collect();
    let mut wanted = theorem("Real.exp_le_exp_of_le", "mathlib", "M", "LE.le", &[]);
    wanted.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![
            ArgHead::Named(DeclName::new("Real")),
            ArgHead::Any,
            ArgHead::Named(DeclName::new("Real.exp")),
            ArgHead::Named(DeclName::new("Real.exp")),
        ],
    );
    rows.push(wanted);
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();

    let mut q = Query::new();
    q.limit = 5;
    q.shape = Shape::new(
        Some(DeclName::new("LE.le")),
        vec![ArgHead::Named(DeclName::new("Real.exp")), ArgHead::Named(DeclName::new("Real.exp"))],
    );
    let hits = db.find(&q).unwrap();
    assert_eq!(
        hits.iter().map(|d| d.name.to_string()).collect::<Vec<_>>(),
        ["Real.exp_le_exp_of_le"]
    );
}
