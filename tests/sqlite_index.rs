//! The SQLite adapter against the real engine: rows survive a round trip, the
//! domain's query rule and the SQL agree, and an elaborated row wins over a
//! text row with the same name.

mod support;

use discrtree::application::index;
use discrtree::application::ports::{DeclRepo, DeclSink, Provenance};
use discrtree::application::status;
use discrtree::domain::decl::{ArgHead, DeclKind, Shape, Span};
use discrtree::domain::name::DeclName;
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use discrtree::infrastructure::revision;
use discrtree::infrastructure::sqlite::SqliteIndex;
use support::{FakeRevisions, TempDir, theorem};

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

/// Provenance is what makes an incremental `dt index` possible and a stale
/// index visible. It has to survive being closed and reopened, because that is
/// the only case that matters: within one run the answer is already in hand.
#[test]
fn provenance_survives_a_reopen() {
    let dir = TempDir::new("dt-provenance");
    let path = dir.path().join("index.db");
    let id = SourceId::new("mathlib");
    let was = Provenance {
        revision: Some("0df444a360ea".into()),
        stamp: Some("12345:1700000000".into()),
        indexed_at: 1_700_000_000,
        decls: 225_508,
    };
    {
        let mut db = SqliteIndex::open(&path).unwrap();
        db.record(&id, &was).unwrap();
    }
    let db = SqliteIndex::open(&path).unwrap();
    assert_eq!(db.provenance(&id).unwrap(), Some(was));
    assert_eq!(db.provenance(&SourceId::new("flt")).unwrap(), None);
}

/// `dt find`, `dt show` and `dt deps` warn about a stale source without paying
/// for the row counts `dt status` prints, so the comparison lives apart from
/// `Status::run` and has to be held to the same rule: both revisions known and
/// different, never one of them.
#[test]
fn a_source_is_stale_only_when_both_revisions_are_known_and_differ() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let p = |rev: Option<&str>| Provenance {
        revision: rev.map(str::to_string),
        stamp: rev.map(str::to_string),
        indexed_at: 1,
        decls: 1,
    };
    db.record(&SourceId::new("project"), &p(Some("4f21c8e"))).unwrap();
    db.record(&SourceId::new("mathlib"), &p(Some("0df444a"))).unwrap();
    // Indexed from a directory nobody could fingerprint at the time.
    db.record(&SourceId::new("flt"), &p(None)).unwrap();

    let revs = FakeRevisions::at(&[
        ("project", "9ab0d31"), // rebuilt since the dump
        ("mathlib", "0df444a"), // where it was
        ("flt", "ccccccc"),     // a revision now, but nothing to compare it to
    ]);
    let ids = ["project", "mathlib", "flt", "never-indexed"].map(SourceId::new);
    let stale = status::stale_among(&db, &revs, ids).unwrap();
    assert_eq!(stale, vec![SourceId::new("project")]);
}

/// The bug this comparison was added for: a local source whose revision is a
/// fingerprint of the build tree, and a module compiled after the last dump.
/// Before the build had a revision this read as "up to date" and `dt find`
/// answered `no match` for a declaration that was in the project all along.
#[test]
fn a_module_compiled_after_the_dump_makes_the_project_stale() {
    let dir = TempDir::new("dt-build-rev");
    let lib = dir.path().join(".lake/build/lib/lean/Transformer");
    std::fs::create_dir_all(&lib).unwrap();
    std::fs::write(lib.join("Hull.olean"), "compiled").unwrap();
    let dumped = revision::build_stamp(dir.path()).expect("a built project has a revision");

    let mut db = SqliteIndex::in_memory().unwrap();
    let id = SourceId::new("project");
    db.record(
        &id,
        &Provenance {
            revision: Some(dumped.clone()),
            stamp: Some("1:1".into()),
            indexed_at: 1,
            decls: 718,
        },
    )
    .unwrap();

    let unchanged = OneBuild(dir.path().to_path_buf());
    assert!(status::stale_among(&db, &unchanged, [id.clone()]).unwrap().is_empty());

    std::fs::write(lib.join("HullProbe.olean"), "compiled since").unwrap();
    assert_ne!(revision::build_stamp(dir.path()).as_deref(), Some(dumped.as_str()));
    assert_eq!(status::stale_among(&db, &unchanged, [id.clone()]).unwrap(), vec![id]);
}

/// Every source is at whatever the build tree under this root fingerprints to,
/// which is what the real adapter does for a `local` source.
struct OneBuild(std::path::PathBuf);

impl discrtree::application::ports::Revisions for OneBuild {
    fn current(&self, _source: &SourceId) -> discrtree::error::Result<Option<String>> {
        Ok(revision::build_stamp(&self.0))
    }
}

/// A second recording replaces the first. A source has one provenance, not a
/// history: what matters is what is in the index now.
#[test]
fn re_indexing_replaces_the_provenance() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let id = SourceId::new("flt");
    let stamp = |rev: &str| Provenance {
        revision: Some(rev.into()),
        stamp: Some(rev.into()),
        indexed_at: 1,
        decls: 1,
    };
    db.record(&id, &stamp("aaaaaaa")).unwrap();
    db.record(&id, &stamp("bbbbbbb")).unwrap();
    assert_eq!(db.provenance(&id).unwrap().unwrap().revision.as_deref(), Some("bbbbbbb"));
}

/// `CREATE TABLE IF NOT EXISTS` would open a database written by an older
/// build, change nothing, and let every later query read a shape that is not
/// there. Refusing is the only answer that cannot silently be wrong.
/// Replacing a source deletes its side rows in the middle of a load, when the
/// one droppable index is down. The delete therefore has to search by
/// something no load can take away: the `WITHOUT ROWID` primary key, which is
/// the table itself rather than an index beside it.
///
/// The first version of the bulk load dropped an index this delete needed, and
/// re-indexing one source in place went from two minutes to over eighteen. The
/// query plan is where that shows up before the wall clock does.
#[test]
fn replacing_a_source_searches_by_a_key_no_load_can_drop() {
    let dir = TempDir::new("dt-plan");
    let path = dir.path().join("index.db");
    let mut db = SqliteIndex::open(&path).unwrap();
    // Loading is what takes the index down, and `clear_source` runs after it.
    index::load(&mut db, &[theorem("A", "mathlib", "M", "Eq", &["Real.exp"])]).unwrap();

    let conn = rusqlite::Connection::open(&path).unwrap();
    for table in ["uses", "dep"] {
        let sql = format!(
            "EXPLAIN QUERY PLAN DELETE FROM {table} \
             WHERE decl_id IN (SELECT id FROM decl WHERE source = 'mathlib')"
        );
        let plan = conn
            .prepare(&sql)
            .unwrap()
            .query_map([], |r| r.get::<_, String>(3))
            .unwrap()
            .collect::<Result<Vec<String>, _>>()
            .unwrap()
            .join("; ");
        assert!(
            plan.contains(&format!("SEARCH {table} USING PRIMARY KEY")),
            "the delete over `{table}` must not scan: {plan}"
        );
    }
}

#[test]
fn an_index_from_another_schema_is_refused_rather_than_misread() {
    let dir = TempDir::new("dt-schema");
    let path = dir.path().join("index.db");
    SqliteIndex::open(&path).unwrap();
    rusqlite::Connection::open(&path).unwrap().pragma_update(None, "user_version", 99i64).unwrap();
    let err = match SqliteIndex::open(&path) {
        Err(e) => e.to_string(),
        Ok(_) => panic!("an index from schema 99 must not open"),
    };
    assert!(err.contains("different version of dt"), "got: {err}");
    assert!(err.contains("--rebuild"), "the error has to say what to do: {err}");
}

/// A file with nothing in it is new, not foreign. Refusing to create an index
/// would make the tool unusable on first run.
#[test]
fn an_empty_file_is_a_new_index() {
    let dir = TempDir::new("dt-fresh");
    let path = dir.path().join("index.db");
    std::fs::write(&path, b"").unwrap();
    assert!(SqliteIndex::open(&path).is_ok());
}

/// An index of this many rows makes one source a small share of it. The
/// decision is a fraction, so a three-row index has no small loads and this
/// number is the smallest one that gives the maintained path something to do.
const ENOUGH_TO_BE_BIG: usize = 320;

fn filled(db: &mut SqliteIndex) {
    let rows: Vec<_> = (0..ENOUGH_TO_BE_BIG)
        .map(|i| theorem(&format!("Mathlib.pad{i}"), "mathlib", "Mathlib.Pad", "Eq", &[]))
        .collect();
    db.clear_source(&SourceId::new("mathlib")).unwrap();
    index::load(db, &rows).unwrap();
    db.finish().unwrap();
}

fn text_matches(db: &SqliteIndex, word: &str) -> Vec<String> {
    let mut q = Query::new();
    q.text = Some(word.to_string());
    db.find(&q).unwrap().iter().map(|d| d.name.to_string()).collect()
}

/// Re-indexing one edited source used to rebuild the text index over every row
/// in the database — six seconds of a fourteen-second `dt index` that had
/// 1864 rows to write. A load small enough to maintain does not rebuild, and
/// the only thing that can be observed from outside is whether `--text` is
/// still right: both halves have to hold, the rows that left must stop
/// matching and the rows that arrived must start.
#[test]
fn a_small_load_keeps_the_text_index_current_without_rebuilding_it() {
    let mut db = SqliteIndex::in_memory().unwrap();
    filled(&mut db);

    let mut first = theorem("Transformer.hullProbe", "project", "Transformer.ALM", "Eq", &[]);
    first.ty = "hullProbe is monotone".into();
    db.clear_source(&SourceId::new("project")).unwrap();
    index::load(&mut db, &[first]).unwrap();
    db.finish().unwrap();
    assert_eq!(text_matches(&db, "hullProbe"), vec!["Transformer.hullProbe".to_string()]);

    // The edit: the same source, dumped again, with the declaration renamed.
    let mut second = theorem("Transformer.softmaxIndex", "project", "Transformer.ALM", "Eq", &[]);
    second.ty = "softmaxIndex is monotone".into();
    db.clear_source(&SourceId::new("project")).unwrap();
    index::load(&mut db, &[second]).unwrap();
    db.finish().unwrap();
    assert_eq!(text_matches(&db, "softmaxIndex"), vec!["Transformer.softmaxIndex".to_string()]);
    assert!(text_matches(&db, "hullProbe").is_empty(), "the deleted row still matches");
}

/// A row rewritten inside one load is deleted and inserted again under a new
/// id. The text index is keyed on the old one, and nothing but `decl` can say
/// what that row said — so the entry has to go before the row does, or the old
/// text keeps matching an id no declaration has.
#[test]
fn a_row_rewritten_within_a_load_takes_its_old_text_with_it() {
    let mut db = SqliteIndex::in_memory().unwrap();
    filled(&mut db);
    db.clear_source(&SourceId::new("project")).unwrap();

    let mut was = theorem("Transformer.probe", "project", "Transformer.ALM", "Eq", &[]);
    was.ty = "hullProbe is monotone".into();
    index::load(&mut db, &[was]).unwrap();

    let mut now = theorem("Transformer.probe", "project", "Transformer.ALM", "Eq", &[]);
    now.ty = "softmaxIndex is monotone".into();
    index::load(&mut db, &[now]).unwrap();
    db.finish().unwrap();

    assert_eq!(text_matches(&db, "softmaxIndex"), vec!["Transformer.probe".to_string()]);
    assert!(text_matches(&db, "hullProbe").is_empty(), "the overwritten text still matches");
}

/// The two tests above would pass on the old code too: a rebuild also leaves
/// the text index right. What tells the paths apart is the work `finish` does
/// not do, and the planner's statistics are where that becomes visible —
/// `ANALYZE` is one of the three fixed prices, so after a maintained load the
/// numbers must still be the ones the last bulk load wrote.
#[test]
fn a_maintained_load_leaves_the_fixed_prices_unpaid() {
    let dir = TempDir::new("dt-maintained");
    let path = dir.path().join("index.db");
    let mut db = SqliteIndex::open(&path).unwrap();
    filled(&mut db);

    let stat = || -> Option<String> {
        rusqlite::Connection::open(&path)
            .unwrap()
            .query_row(
                "SELECT stat FROM sqlite_stat1 WHERE tbl = 'decl' AND idx = 'decl_lookup'",
                [],
                |r| r.get(0),
            )
            .ok()
    };
    let before = stat();
    assert!(before.is_some(), "the bulk load must have analyzed, or this proves nothing");

    db.clear_source(&SourceId::new("project")).unwrap();
    index::load(&mut db, &[theorem("Transformer.probe", "project", "Transformer.ALM", "Eq", &[])])
        .unwrap();
    db.finish().unwrap();
    assert_eq!(before, stat(), "a one-row load re-analyzed the whole index");
    // FTS5 checks an external-content index against the table it indexes,
    // which is the one question the maintained path has to answer for itself.
    rusqlite::Connection::open(&path)
        .unwrap()
        .execute_batch("INSERT INTO decl_fts(decl_fts, rank) VALUES('integrity-check', 1);")
        .expect("the maintained text index no longer matches the rows it indexes");

    // And the other way: a load that replaces the big source does pay, because
    // for that one the fixed price is the cheaper answer.
    filled(&mut db);
    assert_ne!(before, stat(), "a full reload must leave the statistics current");
}
