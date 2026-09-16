//! The SQLite adapter against the real engine: rows survive a round trip, the
//! domain's query rule and the SQL agree, and an elaborated row wins over a
//! text row with the same name.

mod support;

use discrtree::application::index;
use discrtree::application::ports::{DeclRepo, DeclSink, Provenance};
use discrtree::application::status;
use discrtree::domain::decl::{ArgHead, Decl, DeclKind, Shape, Span};
use discrtree::domain::name::{DeclName, ModuleName};
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

/// The SQL counts the same thing the in-memory stores count, which is the
/// only reason a pattern means the same in a project with an index and in one
/// reading its dumps directly. `Inner.inner` heads two rows here and
/// `Std.HashMap.inner` one, and the `LIKE` that fetches them is a filter, not
/// the answer.
#[test]
fn an_unqualified_word_resolves_to_the_commonest_constant_called_that() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let head = |name: &str, arg: &str, ty: &str| {
        let mut d = theorem(name, "mathlib", "Mathlib.Analysis.Inner", "Eq", &[]);
        d.ty = ty.into();
        d.consts = vec![DeclName::new(arg)];
        d.shape = Shape::new(
            Some(DeclName::new("Eq")),
            vec![ArgHead::Named(DeclName::new(arg)), ArgHead::Any],
        );
        d
    };
    let rows = vec![
        head("Real.inner_apply", "Inner.inner", "inner ℝ x y = x * y"),
        head("Complex.inner_apply", "Inner.inner", "inner ℂ x y = conj x * y"),
        head("Std.HashMap.inner_eq", "Std.HashMap.inner", "inner m = m"),
        // Printed with its namespace, so it says nothing about the bare word.
        head("Std.HashMap.inner_size", "Std.HashMap.inner", "m.inner.size = m.size"),
        head("Std.HashMap.inner_empty", "Std.HashMap.inner", "m.inner = ∅"),
    ];
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    let called = db.heads_called("inner").unwrap();
    assert_eq!(
        called.iter().map(|c| c.as_str()).collect::<Vec<_>>(),
        ["Inner.inner", "Std.HashMap.inner"]
    );
    // A word nothing is called resolves to nothing, rather than to whatever
    // the `LIKE` happened to sweep up.
    assert!(db.heads_called("nonesuch").unwrap().is_empty());
    // A word the index holds by exactly that spelling is a constant; one only
    // namespaces end in is not.
    assert!(db.is_constant(&DeclName::new("Inner.inner")).unwrap());
    assert!(db.is_constant(&DeclName::new("Real.inner_apply")).unwrap());
    assert!(!db.is_constant(&DeclName::new("inner")).unwrap());
}

/// A field is a whole last component: `.le_exp` does not end `exp_le_exp`.
#[test]
fn a_field_names_the_declarations_that_end_in_it() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let rows = vec![
        theorem("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Exp", "LE.le", &["Real.exp"]),
        theorem("Finset.sum_le_sum", "mathlib", "Mathlib.Algebra.Order", "LE.le", &[]),
        theorem("Complex.exp", "mathlib", "Mathlib.Analysis.Exp", "Eq", &[]),
        theorem("Real.exp", "mathlib", "Mathlib.Analysis.Exp", "Eq", &[]),
    ];
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    let ending = |f: &str| {
        db.ending_in(&DeclName::new(f))
            .unwrap()
            .into_iter()
            .map(|n| n.into_string())
            .collect::<Vec<_>>()
    };
    assert_eq!(ending(".exp_le_exp"), ["Real.exp_le_exp"]);
    assert_eq!(ending(".le_exp"), Vec::<String>::new());
    assert_eq!(ending(".sum_le_sum"), ["Finset.sum_le_sum"]);
    // The one statements mention comes first, whatever its name.
    assert_eq!(ending(".exp"), ["Real.exp", "Complex.exp"]);
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

/// A field -- `.length`, which `l.length` in a pattern comes to -- names its
/// constant in any namespace wherever a name is asked for: as the conclusion,
/// as an argument, and as a condition, which nothing after the SQL checks
/// again. A whole component, in the case it is written in, and the `?` of
/// `head?` a letter.
#[test]
fn a_field_names_its_constant_in_any_namespace() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut nodup =
        theorem("A.nodup", "mathlib", "M", "List.Nodup", &["List.length", "List.head?"]);
    nodup.shape.args = vec![ArgHead::Any, ArgHead::Named(DeclName::new("List.reverse"))];
    let mut other =
        theorem("B.eq", "mathlib", "M", "Eq", &["B.Length", "List.lengthTR", "List.headX"]);
    other.shape.args = vec![ArgHead::Any, ArgHead::Named(DeclName::new("B.Reverse"))];
    index::load(&mut db, &[nodup, other]).unwrap();
    db.finish().unwrap();
    let names = |concl: Option<&str>, args: &[&str], uses: &[&str]| -> Vec<String> {
        let mut q = Query::new();
        let args = args.iter().map(|a| ArgHead::Named(DeclName::new(*a))).collect();
        q.shape = Shape::new(concl.map(DeclName::new), args);
        q.uses = uses.iter().map(|u| DeclName::new(*u)).collect();
        db.find(&q).unwrap().into_iter().map(|d| d.name.to_string()).collect()
    };
    assert_eq!(names(Some(".Nodup"), &[], &[]), ["A.nodup"]);
    assert!(names(Some(".nodup"), &[], &[]).is_empty());
    assert!(names(Some(".odup"), &[], &[]).is_empty());
    assert_eq!(names(None, &[".reverse"], &[]), ["A.nodup"]);
    assert_eq!(names(None, &[".Reverse"], &[]), ["B.eq"]);
    assert_eq!(names(None, &[], &[".length"]), ["A.nodup"]);
    assert_eq!(names(None, &[], &[".Length"]), ["B.eq"]);
    assert_eq!(names(None, &[], &[".head?"]), ["A.nodup"]);
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
    let sources: Vec<SourceId> =
        db.named(&DeclName::new("Foo.bar")).unwrap().into_iter().map(|d| d.source).collect();
    assert_eq!(sources, [SourceId::new("mathlib"), SourceId::new("flt")], "elaborated first");
}

/// `RestrictedProduct.singleAddMonoidHom` has fourteen dependencies read off
/// its proof in Mathlib, and three more a scanner guessed from FLT's text. The
/// lists were read by name, and both rows had all seventeen.
#[test]
fn rows_that_share_a_name_keep_their_own_lists() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let compiled = theorem("Foo.bar", "mathlib", "Mathlib.Foo", "Eq", &["Nat.add"]);
    let mut text = theorem("Foo.bar", "flt", "FLT.Foo", "Eq", &["Pi.single"]);
    text.elaborated = false;
    index::load(&mut db, &[text, compiled]).unwrap();
    db.finish().unwrap();

    let lists = |d: &Decl| (d.source.to_string(), d.deps.clone(), d.consts.clone());
    let own = |source: &str, dep: &str| {
        (source.to_string(), vec![DeclName::new(dep)], vec![DeclName::new(dep)])
    };
    let name = DeclName::new("Foo.bar");
    let rows: Vec<_> = db.named(&name).unwrap().iter().map(lists).collect();
    assert_eq!(rows, [own("mathlib", "Nat.add"), own("flt", "Pi.single")]);
    assert_eq!(lists(&db.get(&name).unwrap().unwrap()), own("mathlib", "Nat.add"));
    let many: Vec<_> = db.get_many(&[name]).unwrap().iter().map(lists).collect();
    assert_eq!(many, [own("mathlib", "Nat.add")]);
    let flt = Query { source: Some(SourceId::new("flt")), ..Query::new() };
    let found: Vec<_> = db.find(&flt).unwrap().iter().map(lists).collect();
    assert_eq!(found, [own("flt", "Pi.single")]);
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
        ..Provenance::by_this_build()
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
        ..Provenance::by_this_build()
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
    assert_eq!(
        stale,
        vec![status::Stale {
            id: SourceId::new("project"),
            why: status::Why::Moved { indexed: "4f21c8e".into(), current: "9ab0d31".into() },
        }]
    );
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
            ..Provenance::by_this_build()
        },
    )
    .unwrap();

    let unchanged = OneBuild(dir.path().to_path_buf());
    assert!(status::stale_among(&db, &unchanged, [id.clone()]).unwrap().is_empty());

    std::fs::write(lib.join("HullProbe.olean"), "compiled since").unwrap();
    assert_ne!(revision::build_stamp(dir.path()).as_deref(), Some(dumped.as_str()));
    let stale = status::stale_among(&db, &unchanged, [id.clone()]).unwrap();
    assert_eq!(stale.iter().map(|s| s.id.clone()).collect::<Vec<_>>(), vec![id]);
    // What differs is the build, and the line that reports it has to be able
    // to show both values rather than assert a move.
    let status::Why::Moved { indexed, current } = &stale[0].why else {
        panic!("a rebuilt project moved, {:?}", stale[0].why)
    };
    assert_eq!(indexed, &dumped);
    assert_ne!(current, &dumped);
}

/// `dt show` printed rows, and a rebuild makes them stale only if it compiled
/// their module again. A build elsewhere in the project moves the source, but
/// the row shown from an untouched module is neither missing nor out of date.
#[test]
fn a_shown_row_is_stale_only_when_its_own_module_was_rebuilt() {
    let dir = TempDir::new("dt-module-rev");
    let lib = dir.path().join(".lake/build/lib");
    let pkg = lib.join("lean/Transformer/CRASP");
    std::fs::create_dir_all(&pkg).unwrap();
    std::fs::write(pkg.join("Basic.olean"), "compiled").unwrap();
    let dumped = revision::build_stamp(&lib).unwrap();
    let written = std::fs::metadata(pkg.join("Basic.olean")).unwrap().modified().unwrap();
    let indexed_at = written.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() + 100;

    let mut db = SqliteIndex::in_memory().unwrap();
    let id = SourceId::new("project");
    let was =
        Provenance { revision: Some(dumped), indexed_at, decls: 1, ..Provenance::by_this_build() };
    db.record(&id, &was).unwrap();
    let disk = revision::OnDisk {
        checkouts: Default::default(),
        builds: [(id.clone(), lib.clone())].into(),
        manifest: Default::default(),
        toolchains: Default::default(),
    };
    let shown = |module: &str| {
        let mut rows = std::collections::BTreeMap::new();
        rows.insert(id.clone(), [ModuleName::new(module)].into());
        status::stale_for_rows(&db, &disk, &rows).unwrap()
    };

    std::fs::write(pkg.join("Hull.olean"), "compiled since").unwrap();
    assert_eq!(status::stale_among(&db, &disk, [id.clone()]).unwrap().len(), 1);
    assert!(shown("Transformer.CRASP.Basic").is_empty(), "Basic was not rebuilt");
    // A module whose file cannot be found is not known to be untouched.
    assert_eq!(shown("Transformer.CRASP.Gone").len(), 1);

    let later = std::time::UNIX_EPOCH + std::time::Duration::from_secs(indexed_at + 100);
    std::fs::File::options()
        .write(true)
        .open(pkg.join("Basic.olean"))
        .unwrap()
        .set_modified(later)
        .unwrap();
    assert_eq!(shown("Transformer.CRASP.Basic").len(), 1, "Basic was rebuilt");
}

/// A rebuild that compiled a module again without changing what it declares
/// leaves every row the search could want in the index, and the line that
/// said otherwise after every `lake build` went unread. A declaration the
/// index has no row for, or has at other lines, is what makes it stale.
#[test]
fn a_rebuild_is_stale_for_a_search_only_when_it_declares_what_the_index_lacks() {
    let dir = TempDir::new("dt-ilean-rev");
    let lib = dir.path().join(".lake/build/lib");
    let pkg = lib.join("lean/Transformer/CRASP");
    std::fs::create_dir_all(&pkg).unwrap();
    std::fs::write(pkg.join("Basic.olean"), "compiled").unwrap();
    let dumped = revision::build_stamp(&lib).unwrap();
    let written = std::fs::metadata(pkg.join("Basic.olean")).unwrap().modified().unwrap();
    let indexed_at = written.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs() - 100;

    let id = SourceId::new("project");
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut row = theorem("T.depth_le", "project", "Transformer.CRASP.Basic", "LE.le", &[]);
    row.span = Some(Span::new(109, 111));
    db.put(&[row]).unwrap();
    db.finish().unwrap();
    let was =
        Provenance { revision: Some(dumped), indexed_at, decls: 1, ..Provenance::by_this_build() };
    db.record(&id, &was).unwrap();
    let disk = revision::OnDisk {
        checkouts: Default::default(),
        builds: [(id.clone(), lib.clone())].into(),
        manifest: Default::default(),
        toolchains: Default::default(),
    };
    std::fs::write(pkg.join("Basic.olean"), "compiled again").unwrap();
    let declaring = |decls: &str| {
        std::fs::write(pkg.join("Basic.ilean"), format!(r#"{{"version":2,"decls":{{{decls}}}}}"#))
            .unwrap();
        status::stale_for_search(&db, &disk, [id.clone()]).unwrap().len()
    };

    assert_eq!(status::stale_among(&db, &disk, [id.clone()]).unwrap().len(), 1);
    let same = r#""T.depth_le":[108,0,110,7,108,16,108,24]"#;
    assert_eq!(declaring(same), 0, "the rebuild declares what the index holds");
    let private = r#""_private.Transformer.CRASP.Basic.0.T.aux":[1,0,2,7,1,4,1,7]"#;
    assert_eq!(declaring(&format!("{same},{private}")), 0, "a private name has no row");
    assert_eq!(declaring(&format!("{same},\"T.depth_or\":[94,0,94,91,94,16,94,24]")), 1);
    assert_eq!(declaring(r#""T.depth_le":[120,0,122,7,120,16,120,24]"#), 1, "it moved");
    std::fs::remove_file(pkg.join("Basic.ilean")).unwrap();
    assert_eq!(status::stale_for_search(&db, &disk, [id]).unwrap().len(), 1, "unreadable");
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
        ..Provenance::by_this_build()
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
    q.text = vec![word.to_string()];
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

/// `--name` is a substring filter, and the rows it matches are cut to a window
/// before the domain ranks them. A name that is also a namespace matches more
/// rows than the window holds, so the one called exactly that has to be inside
/// it: outside, no ranking can put it first, because it is not there at all.
#[test]
fn the_row_called_exactly_what_was_asked_for_is_inside_the_window() {
    let mut db = SqliteIndex::in_memory().unwrap();
    // Enough descendants to fill the window several times over, all of them
    // matching the substring, none of them the row that was asked for -- and
    // written first, so that the row that was asked for is past the window in
    // the order the rows happen to be stored.
    let mut rows: Vec<_> = (0..300)
        .map(|i| {
            theorem(
                &format!("Real.sin_sq_le_{i}"),
                "mathlib",
                "Mathlib.Analysis.Trig",
                "LE.le",
                &[],
            )
        })
        .collect();
    rows.push(theorem("Real.sin_sq", "mathlib", "Mathlib.Analysis.Trig", "Eq", &[]));
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    let mut q = Query::new();
    q.name = Some("Real.sin_sq".into());
    let got = db.find(&q).unwrap();
    assert!(
        got.iter().any(|d| d.name.as_str() == "Real.sin_sq"),
        "the exact row is missing from the window entirely"
    );
}

/// The index the user upgraded into: rows written by an older `dt`, a source
/// that has not moved, and a `dt status` that reported neither. Two things have
/// to hold at once. The file must still open — refusing it would mean rebuilding
/// 1.2 GB to learn a fact the empty column already states — and the source must
/// come back as behind, because the rows in it are not the rows this build
/// writes.
#[test]
fn an_index_written_by_an_older_dt_opens_and_says_so() {
    let dir = TempDir::new("dt-writer");
    let path = dir.path().join("index.db");
    let id = SourceId::new("mathlib");
    {
        let mut db = SqliteIndex::open(&path).unwrap();
        index::load(&mut db, &[theorem("Real.exp_pos", "mathlib", "M", "LT.lt", &[])]).unwrap();
        db.record(
            &id,
            &Provenance {
                revision: Some("5ed2965".into()),
                stamp: Some("5ed2965".into()),
                indexed_at: 1,
                decls: 1,
                ..Provenance::by_this_build()
            },
        )
        .unwrap();
    }
    // What a dt from before the writer was recorded left behind: the same rows,
    // the same revision, and no answer to the question of who wrote them.
    let conn = rusqlite::Connection::open(&path).unwrap();
    conn.execute_batch(
        "ALTER TABLE source DROP COLUMN writer; ALTER TABLE source DROP COLUMN row_format;",
    )
    .unwrap();
    conn.pragma_update(None, "user_version", 2i64).unwrap();
    drop(conn);

    let db = SqliteIndex::open(&path).expect("an older index is migrated, not refused");
    assert_eq!(db.count_source(&id).unwrap(), 1, "the rows survive the migration");
    let was = db.provenance(&id).unwrap().unwrap();
    assert_eq!(was.writer, None);
    assert!(was.outdated(), "rows nobody stamped are older than this build's");

    // The revision has not moved, which is exactly why the old check said
    // nothing and this one has to.
    let revs = FakeRevisions::at(&[("mathlib", "5ed2965")]);
    let stale = status::stale_among(&db, &revs, [id.clone()]).unwrap();
    assert_eq!(stale, vec![status::Stale { id, why: status::Why::Written { by: None } }]);
}

/// A source that moved *and* holds old rows is reported as moved. Both repairs
/// end in a load, and only one of them starts with an hour of Lean: saying
/// "moved" is what asks for it.
#[test]
fn a_source_that_moved_and_was_written_by_an_older_dt_is_reported_as_moved() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let id = SourceId::new("mathlib");
    db.record(
        &id,
        &Provenance {
            revision: Some("5ed2965".into()),
            stamp: None,
            indexed_at: 1,
            decls: 1,
            writer: Some("0.22.0".into()),
            row_format: Some(0),
        },
    )
    .unwrap();
    let revs = FakeRevisions::at(&[("mathlib", "4f8b12c")]);
    let stale = status::stale_among(&db, &revs, [id]).unwrap();
    assert!(stale[0].why.needs_reread(), "a moved source is read again: {:?}", stale[0].why);
}

/// `used_by` reads both side tables, and the SQL filter on generated names
/// agrees with `Decl::is_generated`.
#[test]
fn what_mentions_a_name_is_read_from_proofs_and_statements() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut in_proof = theorem("B.proof", "mathlib", "Mathlib.B", "Eq", &["Real.exp"]);
    in_proof.consts.clear();
    let mut elim = theorem("Form.and.elim", "project", "T", "Eq", &["Real.exp"]);
    elim.ty = "(t : Form) → t.ctorIdx = 3 → motive t".into();
    let rows = vec![
        theorem("A.stated", "mathlib", "Mathlib.A", "Eq", &["Real.exp"]),
        in_proof,
        theorem("Form.ctorIdx", "project", "T", "Eq", &["Real.exp"]),
        elim,
        theorem("Or.elim", "project", "T", "Eq", &["Real.exp"]),
        theorem("C.unrelated", "mathlib", "Mathlib.A", "Eq", &["Real.log"]),
    ];
    index::load(&mut db, &rows).unwrap();
    db.finish().unwrap();
    let root = DeclName::new("Real.exp");

    let names = |q: &Query| {
        let mut got: Vec<(String, bool)> = db
            .used_by(&root, q)
            .unwrap()
            .into_iter()
            .map(|m| (m.decl.name.to_string(), m.in_statement))
            .collect();
        got.sort();
        got
    };
    let own = |s: &str| (s.to_string(), true);
    assert_eq!(
        names(&Query::new()),
        vec![own("A.stated"), ("B.proof".to_string(), false), own("Or.elim")]
    );
    let mut all = Query::new();
    all.generated = true;
    assert_eq!(names(&all).len(), 5);
    let mut within = Query::new();
    within.module = Some("Mathlib".into());
    assert_eq!(names(&within).len(), 2, "a module prefix covers its children");
    within.source = Some(SourceId::new("project"));
    assert!(names(&within).is_empty());

    let mut named = Query::new();
    named.name = Some("elim".into());
    let found: Vec<String> =
        db.find(&named).unwrap().into_iter().map(|d| d.name.to_string()).collect();
    assert_eq!(found, vec!["Or.elim".to_string()]);
}

/// `dt refresh` records the revision a source had when its read began, and
/// names the sources a build moved before the refresh ended.
#[test]
fn a_source_that_moved_during_its_read_is_named() {
    let before: std::collections::BTreeMap<SourceId, Option<String>> = [
        (SourceId::new("project"), Some("aaaa".to_string())),
        (SourceId::new("mathlib"), Some("bbbb".to_string())),
        (SourceId::new("core"), None),
    ]
    .into();
    let now = FakeRevisions::at(&[("project", "cccc"), ("mathlib", "bbbb"), ("core", "v4")]);
    let moved = status::moved_while_read(&now, &before).unwrap();
    assert_eq!(
        moved,
        vec![status::Stale {
            id: SourceId::new("project"),
            why: status::Why::Moved { indexed: "aaaa".into(), current: "cccc".into() },
        }],
        "an unknown revision is not a move"
    );
}

#[test]
fn a_list_of_kinds_selects_any_of_them() {
    let mut db = SqliteIndex::in_memory().unwrap();
    let mut def = theorem("A.def", "mathlib", "M", "Eq", &[]);
    def.kind = DeclKind::Def;
    let mut opaque = theorem("A.opaque", "mathlib", "M", "Eq", &[]);
    opaque.kind = DeclKind::parse("opaque");
    index::load(&mut db, &[def, opaque, theorem("A.thm", "mathlib", "M", "Eq", &[])]).unwrap();
    db.finish().unwrap();
    let mut q = Query::new();
    q.name = Some("A.".into());
    q.kind = vec![DeclKind::Def, DeclKind::parse("opaque")];
    let mut got: Vec<String> =
        db.find(&q).unwrap().into_iter().map(|d| d.name.to_string()).collect();
    got.sort();
    assert_eq!(got, vec!["A.def", "A.opaque"]);
}
