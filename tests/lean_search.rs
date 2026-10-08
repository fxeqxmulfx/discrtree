mod support;

use discrtree::application::find::Find;
use discrtree::application::index;
use discrtree::application::ports::{DeclRepo, DeclSink, NoBuild};
use discrtree::domain::decl::{Decl, DeclKind};
use discrtree::domain::name::{DeclName, ModuleName};
use discrtree::domain::pattern;
use discrtree::domain::query::Query;
use discrtree::domain::source::SourceId;
use discrtree::infrastructure::jsonl::{self, Row};
use discrtree::infrastructure::lake::{DUMP_LEAN, splice_imports};
use discrtree::infrastructure::sqlite::SqliteIndex;
use std::path::Path;
use std::process::Command;
use support::{FakeRepo, TempDir};

fn fixture() -> Vec<Decl> {
    include_str!("fixtures/search.jsonl")
        .lines()
        .map(|line| Decl::from(serde_json::from_str::<Row>(line).unwrap()))
        .collect()
}

fn core_fixture() -> Vec<Decl> {
    include_str!("fixtures/core-search.jsonl")
        .lines()
        .map(|line| Decl::from(serde_json::from_str::<Row>(line).unwrap()))
        .collect()
}

fn data_fixture() -> Vec<Decl> {
    include_str!("fixtures/data-search.jsonl")
        .lines()
        .map(|line| Decl::from(serde_json::from_str::<Row>(line).unwrap()))
        .collect()
}

fn database(rows: &[Decl]) -> SqliteIndex {
    let mut db = SqliteIndex::in_memory().unwrap();
    index::load(&mut db, rows).unwrap();
    db.finish().unwrap();
    db
}

/// Expectations are names of actual compiled declarations, rather than
/// skeletons constructed to agree with the parser under test.
const CASES: &[(&str, &str)] = &[
    ("@Eq Nat (_ + 1) (Nat.succ _)", "succ_add"),
    ("@Ne Nat 0 (Nat.succ _)", "succ_ne_zero"),
    ("@Eq Nat (_ * _) (_ ^ 2)", "pow_two"),
    ("@Eq Nat (_ ^ 2) (_ ^ 3)", "pow_exponents"),
    ("(_ ^ 2) = (_ ^ 3)", "pow_exponents"),
    ("SearchFixture.InterleavedValues (_ ^ 2) (n * n)", "interleaved_powers"),
    ("@SearchFixture.InterleavedValues (_ ^ 2) _ (n * n)", "interleaved_powers"),
    ("HEq (_ ^ 2) (n * n)", "pow_heq"),
    ("@HEq Nat (_ ^ 2) Nat (n * n)", "pow_heq"),
    ("#[n, m] = #[n, m]", "array_literal"),
    ("#[] = #[]", "array_empty"),
    ("#[n, m].size = 2", "array_literal_size"),
    ("\"Nat.succ + ∀ → [id]\" = \"Nat.succ + ∀ → [id]\"", "string_literal"),
    ("\"a → \\\"foo\\\"\".length = \"a → \\\"foo\\\"\".length", "string_literal_length"),
    ("'a' = 'a'", "char_literal"),
    ("'→' = '→'", "char_literal_symbol"),
    ("'\\'' = '\\''", "char_literal_quote"),
    ("1.25 = 1.25", "scientific_literal"),
    ("1.25e3 = 1.25e3", "scientific_literal_exponent"),
    ("1.25e-3 = 1.25e-3", "scientific_literal_negative_exponent"),
    ("0xff = 255", "hex_literal"),
    ("Nat = _", "nat_type_equality"),
    ("@Eq Nat _ _", "succ_add"),
    ("SearchFixture.BiTypePred Nat", "bitype_nat_int"),
    ("SearchFixture.Interleaved Nat Int", "interleaved_type"),
    ("@SearchFixture.Interleaved Nat _ Int", "interleaved_type"),
    ("↑0 = 0", "nat_cast_zero"),
    ("↑a.natAbs = ↑a.natAbs", "nat_cast_field"),
    ("(p → q) ↔ (p → q)", "iff_imp_left"),
    ("p ↔ q → p", "iff_imp_right"),
    ("(_ <*> _) = _ <*> _", "option_seq"),
    ("(_ <* _) = _ <* _", "option_seq_left"),
    ("(_ *> _) = _ *> _", "option_seq_right"),
    ("(_ >> _) = _ >> _", "option_then"),
    ("(_ <$> _) = _ <$> _", "option_fmap"),
    ("(_ ||| -1) = _ ||| -1", "neg_bit_or"),
    ("Ordering.gt.isGE = true", "constant_receiver_field"),
    ("{ byteIdx := _ } = { byteIdx := _ }", "raw_record"),
    ("⟨0, _⟩ = ⟨0, _⟩", "anonymous_fin"),
    ("(m...n).toList = (m...n).toList", "range_list"),
    ("(m...=n) = (m...=n)", "range_closed"),
    ("(n...*) = (n...*)", "range_unbounded"),
    ("((m + 1)...n).toList = ((m + 1)...n).toList", "range_bounds"),
    ("(m...<n) = (m...<n)", "range_closed_open"),
    ("(m<...n) = (m<...n)", "range_open"),
    ("(m<...<n) = (m<...<n)", "range_open_open"),
    ("(m<...=n) = (m<...=n)", "range_open_closed"),
    ("(m<...*) = (m<...*)", "range_open_unbounded"),
    ("(*...n) = (*...n)", "range_unbounded_open"),
    ("(*...<n) = (*...<n)", "range_unbounded_open_alias"),
    ("(*...=n) = (*...=n)", "range_unbounded_closed"),
    ("(*...* : Std.Rii Nat) = *...*", "range_all"),
    ("let id := Nat.succ 0; id = id", "let_shadow"),
    ("have id := Nat.succ 0; id = id", "have_shadow"),
    ("Nat.succ _ = _ + 1", "succ_add"),
    ("_ + _ = _ + _", "add_comm"),
    ("(_ + _) = (_ + _)", "add_comm"),
    ("_ * _ = _ * _", "mul_comm"),
    ("x ^ 2 = x * x", "pow_two"),
    ("x * x = x ^ 2", "pow_two"),
    ("0 ≤ x * x", "mul_nonneg"),
    ("0 <= x * x", "mul_nonneg"),
    ("0 ≤ x ^ 2", "mul_nonneg"),
    ("0 < Nat.succ _", "succ_pos"),
    ("Nat.succ _ ≠ 0", "succ_ne_zero"),
    ("Nat.succ _ != 0", "succ_ne_zero"),
    ("0 ≠ Nat.succ _", "succ_ne_zero"),
    ("¬ Nat.succ _ = 0", "not_succ_zero"),
    ("Not (Nat.succ _ = 0)", "not_succ_zero"),
    ("¬ (Nat.succ _ = 0)", "not_succ_zero"),
    ("∃ n : Nat, Nat.succ n = 1", "exists_succ"),
    ("Exists (fun n : Nat => Nat.succ n = 1)", "exists_succ"),
    ("¬ (∃ n : Nat, Nat.succ n = 0)", "not_exists"),
    ("(_ ∧ _) ↔ (_ ∧ _)", "iff_and"),
    ("_ = _ → Nat.succ _ = Nat.succ _", "equality_hypothesis"),
    ("_ = _ -> Nat.succ _ = Nat.succ _", "equality_hypothesis"),
    ("∀ (f : Nat → Nat) (n : Nat), f n = f n", "forall_body"),
    ("∀ id : Nat, id + id = id + id", "shadowed_id"),
    ("forall id : Nat, id + id = id + id", "shadowed_id"),
    ("∀ (Nat : Type) (n : Nat), n = n", "shadowed_Nat"),
    ("(∀ Nat : Type, ∀ n : Nat, n = n) ∧ Nat.succ 0 = 1", "scoped_shadow"),
    ("¬ (_ ∈ _) ↔ _ ∉ _", "not_mem_iff"),
    ("¬ (_ → False)", "not_implication"),
    ("∃ f : Nat → Nat, f 0 = 0", "exists_function"),
    ("∃ n : Nat, n = 0 → Nat.succ n = 1", "exists_implication"),
    ("SearchFixture.TypePred (Nat → Nat)", "function_type"),
    ("SearchFixture.TypePred ((Nat → Nat) → Nat)", "nested_function_type"),
    ("SearchFixture.TypePred (List Nat)", "list_type"),
    ("SearchFixture.TypePred Prop", "prop_type"),
    ("SearchFixture.Witness Nat", "natWitness"),
    ("SearchFixture.TypePred SearchFixture.Alias", "alias_type"),
    ("xs ++ [] = xs", "append_nil"),
    ("List.length (_ ++ _) = _ + _", "append_length"),
    ("(xs ++ ys).length = xs.length + ys.length", "append_length"),
    ("xs.reverse.reverse = xs", "reverse_reverse"),
    ("List.reverse (List.reverse _) = _", "reverse_reverse"),
    ("(_ :: _).head? = some _", "head_cons"),
    ("(_ :: _)[0]? = some _", "getElem_cons"),
    ("_ ∉ ([] : List Nat)", "nil_mem"),
    ("Not (_ ∈ ([] : List Nat))", "nil_mem"),
    ("_ ∈ _ :: _", "cons_mem"),
    ("Option.map Nat.succ (some _) = some (Nat.succ _)", "option_map"),
    ("Prod.fst (_, _) = _", "pair_fst"),
    ("(_, _) = (_, _)", "pair_eq"),
    ("(n, m) = (a, b) ↔ n = a ∧ m = b", "pair_iff"),
    ("∀ (n m : Nat), (n, m) = (n, m)", "pair_eq"),
    ("∀ n : Nat, n ^ 2 = n * n", "pow_two"),
    ("∀ id : Nat, id ^ 2 = id * id", "pow_two"),
    ("@Eq Nat (Nat.succ _) (_ + 1)", "succ_add"),
    ("(_ == _) = (_ == _)", "boolean_beq"),
    ("(_ && _) = (_ && _)", "boolean_and"),
    ("(_ || _) = (_ || _)", "boolean_or"),
    ("(_ ^^ _) = (_ ^^ _)", "boolean_xor"),
    ("(!_ ) = !_", "boolean_not"),
    ("(_ <<< _) = (_ <<< _)", "bit_shift_left"),
    ("(_ >>> _) = (_ >>> _)", "bit_shift_right"),
    ("(_ &&& _) = (_ &&& _)", "bit_and"),
    ("(_ ||| _) = (_ ||| _)", "bit_or"),
    ("(_ ^^^ _) = (_ ^^^ _)", "bit_xor"),
    ("(~~~_) = ~~~_", "bit_complement"),
    ("(¬ _) = ¬ _", "equality_rhs_not"),
    ("[_, _] = _ :: _ :: []", "list_literal"),
    ("([] : List Nat) = []", "list_empty"),
    ("[_, _].length = 2", "list_literal_length"),
    ("[].length = 0", "list_empty_length"),
    ("(if _ ≤ _ then _ + 1 else _ * 2) = (if _ ≤ _ then _ + 1 else _ * 2)", "conditional"),
    ("_ + (if _ ≤ _ then 1 else 0) = _ + (if _ ≤ _ then 1 else 0)", "conditional_add"),
    ("SearchFixture.«arrow → + /- sorry» _ = _", "escaped_head"),
    ("SearchFixture.«has.dot» _ = _", "escaped_dot"),
    ("_root_.SearchFixture.«has.dot» _ = _", "escaped_dot"),
    ("SearchFixture.«TypePred» Nat", "nat_type"),
    ("SearchFixture.TypePred { id : Nat // id = id }", "subtype_type"),
    ("∃ (Carrier : Type) (value : Carrier), True", "dependent_exists"),
    ("Nat.succ _ ∈ Nat.succ _ :: _", "succ_mem_cons"),
    ("Nat.succ _ ≍ Nat.succ _", "succ_heq"),
    ("(fun n => n, 0) = (_, _)", "lambda_pair"),
    (
        "(List.map (fun n => match n with | 0 => 0 | n + 1 => n) _).reverse = _",
        "lambda_match_field",
    ),
];

fn exercise(repo: &dyn DeclRepo) {
    for &(written, expected) in CASES {
        // Whole-expression grouping must be transparent, including when the
        // formula starts with a binder or contains an implication.
        for pattern in [written.to_string(), format!("({written})"), format!("(({written}))")] {
            let p = pattern::parse(&pattern);
            assert!(p.unknown.is_empty(), "{pattern}: {:?}", p.unknown);
            let q = Query { limit: 100, ..p.query };
            let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
            let expected = format!("SearchFixture.{expected}");
            assert!(
                hits.rows.iter().any(|d| d.name.as_str() == expected),
                "{pattern} did not find {expected}; query: {q:?}; answer: {hits:?}"
            );
        }
    }
}

#[test]
fn compiled_lean_statements_are_found_in_sqlite_and_in_memory() {
    let rows = fixture();
    exercise(&FakeRepo { decls: rows.clone() });
    exercise(&jsonl::JsonlRepo::from_decls(rows.clone()));
    exercise(&database(&rows));
}

#[test]
fn ascriptions_check_the_argument_type_in_every_repository() {
    let rows = fixture();
    let fake = FakeRepo { decls: rows.clone() };
    let jsonl = jsonl::JsonlRepo::from_decls(rows.clone());
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &jsonl, &db] {
        let find = |text: &str| {
            let q = Query { limit: 1000, ..pattern::parse(text).query };
            let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
            let count = repo.count(&q).unwrap();
            assert_eq!(count, hits.rows.len(), "{text}");
            hits.rows.iter().map(|d| d.name.to_string()).collect::<Vec<_>>()
        };
        let nat = find("SearchFixture.TypedValue (_ : ℕ) = _");
        assert!(nat.contains(&"SearchFixture.typed_nat".into()), "{nat:?}");
        assert!(nat.contains(&"SearchFixture.typed_generic".into()), "{nat:?}");
        assert!(!nat.contains(&"SearchFixture.typed_int".into()), "{nat:?}");
        let int = find("SearchFixture.TypedValue (_ : ℤ) = _");
        assert!(int.contains(&"SearchFixture.typed_int".into()), "{int:?}");
        assert!(int.contains(&"SearchFixture.typed_generic".into()), "{int:?}");
        assert!(!int.contains(&"SearchFixture.typed_nat_mentions_int".into()), "{int:?}");
        let list = find("SearchFixture.TypedValue (_ : List ℕ) = _");
        assert!(list.contains(&"SearchFixture.typed_list_nat".into()), "{list:?}");
        assert!(list.contains(&"SearchFixture.typed_higher_type".into()), "{list:?}");
        assert!(!list.contains(&"SearchFixture.typed_list_int".into()), "{list:?}");
        let any_head = find("_ (_ : Int) = _");
        assert!(any_head.contains(&"SearchFixture.typed_int".into()), "{any_head:?}");
        assert!(!any_head.contains(&"SearchFixture.typed_nat_mentions_int".into()), "{any_head:?}");
        let fun = find("SearchFixture.TypedValue (_ : Nat → Nat) = _");
        assert!(fun.contains(&"SearchFixture.typed_function".into()), "{fun:?}");
        assert!(find("SearchFixture.SameArgs (_ : Nat) (_ : Int)").is_empty());
        let same = find("SearchFixture.SameArgs (_ : Nat) (_ : Nat)");
        assert!(same.contains(&"SearchFixture.typed_same_generic".into()), "{same:?}");
    }
}

#[test]
fn numeric_literals_match_values_at_their_position_in_every_repository() {
    let rows = fixture();
    let fake = FakeRepo { decls: rows.clone() };
    let jsonl = jsonl::JsonlRepo::from_decls(rows.clone());
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &jsonl, &db] {
        let find = |text: &str| {
            let q = Query { limit: 1000, ..pattern::parse(text).query };
            let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
            hits.rows.iter().map(|d| d.name.to_string()).collect::<Vec<_>>()
        };
        for (pattern, wanted, excluded) in [
            ("SearchFixture.TypePred (Fin 3)", "numeral_fin_three", "numeral_fin_four"),
            ("SearchFixture.TypedValue _ = 1", "numeral_one", "numeral_zero"),
            ("SearchFixture.TypedValue _ = 2", "numeral_two", "numeral_one"),
            ("SearchFixture.TypedValue (_ + 1) = _", "numeral_nested_one", "numeral_nested_two"),
            ("SearchFixture.TypedValue (-1) = _", "numeral_negative_one", "numeral_negative_two"),
            ("SearchFixture.TypedValue _ = 0xff", "numeral_hex", "numeral_two"),
            ("SearchFixture.TypedValue _ = 1.25", "numeral_scientific", "numeral_scientific_other"),
            (
                "SearchFixture.TypedValue _ = 125e1",
                "numeral_scientific_positive_exponent",
                "numeral_scientific",
            ),
            (
                "SearchFixture.TypedValue _ = 0.00125",
                "numeral_scientific_negative_exponent",
                "numeral_scientific",
            ),
            ("SearchFixture.TypedValue _ = 0.0", "numeral_scientific_zero", "numeral_scientific"),
            (
                "SearchFixture.TypedValue _ = 0x100000000000000000000000000000000",
                "numeral_large",
                "numeral_hex",
            ),
        ] {
            let names = find(pattern);
            assert!(names.contains(&format!("SearchFixture.{wanted}")), "{pattern}: {names:?}");
            assert!(!names.contains(&format!("SearchFixture.{excluded}")), "{pattern}: {names:?}");
        }
        let names = find("SearchFixture.TypedValue _ = 1");
        assert!(!names.contains(&"SearchFixture.numeral_zero_mentions_one".into()));
        let names = find("SearchFixture.TypedValue _ = 1.25");
        assert!(names.contains(&"SearchFixture.numeral_scientific_trailing_zeroes".into()));
        let names = find("SearchFixture.TypedValue _ = _");
        for name in ["numeral_zero", "numeral_one", "numeral_two", "numeral_hex"] {
            assert!(names.contains(&format!("SearchFixture.{name}")), "{names:?}");
        }
    }
}

#[test]
fn numeric_constraints_move_with_swapped_operands() {
    let rows = fixture();
    let fake = FakeRepo { decls: rows.clone() };
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &db] {
        let q = Query {
            name: Some("numeral_one_reversed".into()),
            ..pattern::parse("SearchFixture.TypedValue _ = 1").query
        };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert!(hits.swapped, "{hits:?}");
        assert_eq!(hits.rows.len(), 1);
        assert_eq!(hits.rows[0].name.as_str(), "SearchFixture.numeral_one_reversed");
    }
}

#[test]
fn numeric_values_filter_before_the_sql_window_and_survive_reopening() {
    let rows = fixture();
    let mut wrong =
        rows.iter().find(|d| d.name.as_str() == "SearchFixture.numeral_zero").unwrap().clone();
    let wanted =
        rows.iter().find(|d| d.name.as_str() == "SearchFixture.numeral_one").unwrap().clone();
    let dir = TempDir::new("numeral-window");
    let path = dir.path().join("index.db");
    {
        let mut db = SqliteIndex::open(&path).unwrap();
        let mut decoys = Vec::new();
        for i in 0..20_001 {
            wrong.name = format!("Decoy.row{i}").into();
            decoys.push(wrong.clone());
        }
        decoys.push(wanted.clone());
        index::load(&mut db, &decoys).unwrap();
        db.finish().unwrap();
    }
    let db = SqliteIndex::open(&path).unwrap();
    let q = Query { limit: 1, ..pattern::parse("SearchFixture.TypedValue _ = 1").query };
    let found = db.find(&q).unwrap();
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, wanted.name);
    assert_eq!(DeclRepo::count(&db, &q).unwrap(), 1);
}

#[test]
fn numeric_queries_require_refreshing_old_rows_instead_of_ignoring_values() {
    for (name, pattern) in [
        ("numeral_zero", "SearchFixture.TypedValue _ = 1"),
        ("numeral_one_reversed", "SearchFixture.TypedValue _ = 1"),
        ("mul_nonneg", "0 ≤ _ ^ 2"),
    ] {
        let mut row = fixture()
            .into_iter()
            .find(|d| d.name.as_str() == format!("SearchFixture.{name}"))
            .unwrap();
        row.term = None;
        let fake = FakeRepo { decls: vec![row.clone()] };
        let db = database(&[row]);
        for repo in [&fake as &dyn DeclRepo, &db] {
            let err = Find { repo, build: &NoBuild }
                .run(&pattern::parse(pattern).query)
                .unwrap_err()
                .to_string();
            assert!(err.contains("numeric literal values were not recorded"), "{err}");
            assert!(err.contains("dt refresh fixture"), "{err}");
            let unbounded = Query { name: Some(format!("SearchFixture.{name}")), ..Query::new() };
            assert!(!Find { repo, build: &NoBuild }.run(&unbounded).unwrap().rows.is_empty());
        }
    }
}

#[test]
fn of_real_equal_one_excludes_zero_and_unspecialized_numerals() {
    // Real Mathlib declarations dumped by lean/dump.lean, including ofNat's
    // symbolic numeral and the ofReal_eq_one equivalence.
    let rows: Vec<Decl> = include_str!("fixtures/numeral-search.jsonl")
        .lines()
        .map(|line| Decl::from(serde_json::from_str::<Row>(line).unwrap()))
        .collect();
    let fake = FakeRepo { decls: rows.clone() };
    let jsonl = jsonl::JsonlRepo::from_decls(rows.clone());
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &jsonl, &db] {
        let q = Query { limit: 15, ..pattern::parse("ENNReal.ofReal _ = 1").query };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert_eq!(hits.rows.len(), 1, "{hits:?}");
        assert_eq!(hits.rows[0].name.as_str(), "ENNReal.ofReal_one");
        assert_eq!(repo.count(&q).unwrap(), 1);
        let hits = Find { repo, build: &NoBuild }
            .run(&pattern::parse("ENNReal.ofReal _ = 0").query)
            .unwrap();
        assert!(hits.rows.iter().any(|d| d.name.as_str() == "ENNReal.ofReal_zero"));
        assert!(hits.rows.iter().any(|d| d.name.as_str() == "ENNReal.ofReal_of_nonpos"));
        assert!(!hits.rows.iter().any(|d| d.name.as_str() == "ENNReal.ofReal_one"));
        let hits = Find { repo, build: &NoBuild }
            .run(&pattern::parse("ENNReal.ofReal _ = 1 ↔ _ = 1").query)
            .unwrap();
        assert_eq!(hits.rows.len(), 1, "{hits:?}");
        assert_eq!(hits.rows[0].name.as_str(), "ENNReal.ofReal_eq_one");
    }
}

/// Compiled with Lean 4.34.1 and dumped by lean/dump.lean, importing
/// Mathlib.Analysis.InnerProductSpace.Basic and Mathlib.Analysis.Quaternion.
fn inner_fixture() -> Vec<Decl> {
    include_str!("fixtures/inner-search.jsonl")
        .lines()
        .map(|line| Decl::from(serde_json::from_str::<Row>(line).unwrap()))
        .collect()
}

#[test]
fn real_inner_on_complex_arguments_excludes_other_carriers_and_inconsistent_specializations() {
    let rows = inner_fixture();
    let fake = FakeRepo { decls: rows.clone() };
    let jsonl = jsonl::JsonlRepo::from_decls(rows.clone());
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &jsonl, &db] {
        for text in
            ["inner ℝ (_ : ℂ) _ = _", "Inner.inner Real (_ : Complex) _ = _", "⟪(_ : ℂ), _⟫_ℝ = _"]
        {
            let q = Query { limit: 100, ..pattern::parse(text).query };
            let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
            let has = |name: &str| hits.rows.iter().any(|d| d.name.as_str() == name);
            assert!(has("Complex.inner"), "{text}: {hits:?}");
            assert!(has("real_inner_comm"), "{text}: {hits:?}");
            assert!(has("inner_zero_right"), "{text}: {hits:?}");
            for wrong in [
                "Real.inner_apply",
                "Quaternion.inner_def",
                "Quaternion.inner_self",
                "PUnit.inner_eq_zero",
                "RCLike.inner_apply",
                "RCLike.inner_apply'",
            ] {
                assert!(!has(wrong), "{text}: incorrectly included {wrong}");
            }
        }
    }
}

#[test]
fn type_constraints_filter_before_the_sql_result_window_and_survive_reopening() {
    let rows = fixture();
    let mut wrong = rows
        .iter()
        .find(|d| d.name.as_str() == "SearchFixture.typed_nat_mentions_int")
        .unwrap()
        .clone();
    let wanted =
        rows.iter().find(|d| d.name.as_str() == "SearchFixture.typed_int").unwrap().clone();
    let dir = TempDir::new("typed-window");
    let path = dir.path().join("index.db");
    {
        let mut db = SqliteIndex::open(&path).unwrap();
        let mut decoys = Vec::new();
        for i in 0..20_001 {
            wrong.name = format!("Decoy.row{i}").into();
            decoys.push(wrong.clone());
        }
        decoys.push(wanted.clone());
        index::load(&mut db, &decoys).unwrap();
        db.finish().unwrap();
    }
    let db = SqliteIndex::open(&path).unwrap();
    let q = Query { limit: 1, ..pattern::parse("SearchFixture.TypedValue (_ : Int) = _").query };
    let found = db.find(&q).unwrap();
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].name, wanted.name);
    assert_eq!(found[0].term, wanted.term);
    assert_eq!(DeclRepo::count(&db, &q).unwrap(), 1);
}

#[test]
fn typed_queries_require_refreshing_rows_written_without_argument_types() {
    let mut rows = inner_fixture();
    for row in &mut rows {
        row.term = None;
    }
    let fake = FakeRepo { decls: rows.clone() };
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &db] {
        let q = pattern::parse("inner ℝ (_ : ℂ) _ = _").query;
        let err = Find { repo, build: &NoBuild }.run(&q).unwrap_err().to_string();
        assert!(err.contains("argument types were not recorded"), "{err}");
        assert!(err.contains("dt refresh mathlib"), "{err}");
        assert!(
            !Find { repo, build: &NoBuild }
                .run(&pattern::parse("inner _ _ _ = _").query)
                .unwrap()
                .rows
                .is_empty()
        );
    }
}

#[test]
fn power_retries_keep_the_type_constraints_inside_each_factor() {
    let rows = inner_fixture();
    let fake = FakeRepo { decls: rows.clone() };
    let db = database(&rows);
    for repo in [&fake as &dyn DeclRepo, &db] {
        let q = pattern::parse("inner ℝ (_ : ℂ) _ ^ 2 ≤ _").query;
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert!(
            hits.rows.iter().any(|d| d.name.as_str() == "real_inner_mul_inner_self_le"),
            "{hits:?}"
        );
        assert!(!hits.respelled.is_empty(), "{hits:?}");
    }
}

#[test]
fn copying_a_printed_lean_statement_finds_its_declaration() {
    let rows = fixture();
    let db = database(&rows);
    for row in rows.iter().filter(|d| d.kind == DeclKind::Theorem && d.shaped()) {
        let parsed = pattern::parse(&row.ty);
        assert!(parsed.unknown.is_empty(), "{}: {:?}", row.ty, parsed.unknown);
        let q = Query { limit: 100, ..parsed.query };
        let hits = Find { repo: &db, build: &NoBuild }.run(&q).unwrap();
        assert!(
            hits.rows.iter().any(|d| d.name == row.name),
            "{}: {}\n{q:?}\n{hits:?}",
            row.name,
            row.ty
        );
    }
}

#[test]
fn printed_standard_library_statements_find_their_original_theorems() {
    let mut core = core_fixture();
    core.extend(data_fixture());
    let mut rows = fixture();
    rows.extend(core.iter().cloned());
    let db = database(&rows);
    let raw = jsonl::JsonlRepo::from_decls(rows.clone());
    let fake = FakeRepo { decls: rows };
    for repo in [&db as &dyn DeclRepo, &raw, &fake] {
        exercise_core(repo, &core);
    }
}

fn exercise_core(repo: &dyn DeclRepo, core: &[Decl]) {
    exercise_core_scoped(repo, core, false);
}

fn exercise_core_scoped(repo: &dyn DeclRepo, core: &[Decl], module_scope: bool) {
    for (i, row) in core.iter().enumerate() {
        if module_scope && i > 0 && i % 2_000 == 0 {
            eprintln!("checked {i} printed statements");
        }
        let parsed = pattern::parse(&row.ty);
        assert!(parsed.unknown.is_empty(), "{}: {:?}", row.name, parsed.unknown);
        let q = Query {
            name: Some(row.name.to_string()),
            module: module_scope.then(|| row.module.to_string()),
            ..parsed.query
        };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert!(
            hits.rows.iter().any(|d| d.name == row.name),
            "{}: {}\n{q:?}\n{hits:?}",
            row.name,
            row.ty
        );
    }
}

#[test]
fn logical_heads_keep_distinct_kinds_of_propositions_apart() {
    let db = database(&fixture());
    for (written, expected) in [
        ("¬ Nat.succ _ = 0", "Not"),
        ("∃ n : Nat, Nat.succ n = 1", "Exists"),
        ("_ ∉ _", "Not"),
        ("_ ∧ _ ↔ _ ∧ _", "Iff"),
    ] {
        let q = pattern::parse(written).query;
        let hits = Find { repo: &db, build: &NoBuild }.run(&q).unwrap();
        assert!(!hits.rows.is_empty(), "{written}");
        assert!(hits.rows.iter().all(|d| d.shape.concl.as_ref().unwrap().as_str() == expected));
    }
}

#[test]
fn implicit_type_arguments_are_not_equality_operands() {
    let rows = fixture();
    let db = database(&rows);
    let fake = FakeRepo { decls: rows.clone() };
    let raw = jsonl::JsonlRepo::from_decls(rows);
    for repo in [&db as &dyn DeclRepo, &fake, &raw] {
        let q = Query { limit: 1000, ..pattern::parse("Nat = _").query };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert_eq!(
            hits.rows.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
            ["SearchFixture.nat_type_equality"],
            "Nat's appearance as Eq's type is not an operand: {hits:?}",
        );
        let q = Query { limit: 1000, ..pattern::parse("SearchFixture.BiTypePred Int").query };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert_eq!(
            hits.rows.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(),
            ["SearchFixture.bitype_int_nat"],
            "a partially applied function fixes its first argument: {hits:?}",
        );
        let q = Query { limit: 1000, ..pattern::parse("@SearchFixture.Interleaved Nat Int").query };
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert!(hits.rows.is_empty(), "@ requires the instance argument as well: {hits:?}");
    }
}

#[test]
fn explicit_equality_preserves_type_arguments_when_swapping_operands() {
    let rows = fixture();
    let db = database(&rows);
    let fake = FakeRepo { decls: rows.clone() };
    let raw = jsonl::JsonlRepo::from_decls(rows);
    for repo in [&db as &dyn DeclRepo, &fake, &raw] {
        let q = pattern::parse("@Eq Nat (_ + 1) (Nat.succ _)").query;
        let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
        assert!(hits.swapped, "{hits:?}");
        assert!(hits.rows.iter().any(|d| d.name.as_str() == "SearchFixture.succ_add"), "{hits:?}");
    }
}

#[test]
fn explicit_applications_rank_powers_in_the_compilers_argument_positions() {
    let row = fixture().into_iter().find(|d| d.name.as_str() == "SearchFixture.pow_two").unwrap();
    for text in ["@Eq Nat (_ ^ 2) (_ * _)", "@Eq Nat (_ ^ 2) (n * n)"] {
        let q = pattern::parse(text).query;
        assert!(discrtree::domain::query::writes_powers(&q, &row), "{text}: {q:?}");
    }
    let q = pattern::parse("@Eq Nat (_ ^ 3) (_ * _)").query;
    assert!(!discrtree::domain::query::writes_powers(&q, &row));
    let mut legacy = row.clone();
    legacy.shape.explicit_args = None;
    let q = pattern::parse("@Eq Nat (_ ^ 2) (n * n)").query;
    assert!(discrtree::domain::query::writes_powers(&q, &legacy));

    let interleaved = fixture()
        .into_iter()
        .find(|d| d.name.as_str() == "SearchFixture.interleaved_powers")
        .unwrap();
    for text in [
        "SearchFixture.InterleavedValues (_ ^ 2) (n * n)",
        "@SearchFixture.InterleavedValues (_ ^ 2) _ (n * n)",
    ] {
        let q = pattern::parse(text).query;
        assert!(discrtree::domain::query::writes_powers(&q, &interleaved), "{text}: {q:?}");
    }
    let heq = fixture().into_iter().find(|d| d.name.as_str() == "SearchFixture.pow_heq").unwrap();
    for text in ["HEq (_ ^ 2) (n * n)", "@HEq Nat (_ ^ 2) Nat (n * n)", "(_ ^ 2) ≍ (n * n)"] {
        let q = pattern::parse(text).query;
        assert!(discrtree::domain::query::writes_powers(&q, &heq), "{text}: {q:?}");
    }
}

#[test]
fn equal_operand_heads_can_still_require_swapping_different_powers() {
    let rows = fixture();
    let db = database(&rows);
    let fake = FakeRepo { decls: rows.clone() };
    let raw = jsonl::JsonlRepo::from_decls(rows);
    for repo in [&db as &dyn DeclRepo, &fake, &raw] {
        for text in ["(_ ^ 2) = (_ ^ 3)", "@Eq Nat (_ ^ 2) (_ ^ 3)"] {
            let q = pattern::parse(text).query;
            let hits = Find { repo, build: &NoBuild }.run(&q).unwrap();
            assert!(hits.swapped, "{text}: {hits:?}");
            assert!(hits.respelled.is_empty(), "{text}: {hits:?}");
            assert!(hits.rows.iter().any(|d| d.name.as_str() == "SearchFixture.pow_exponents"));
        }
    }
}

#[test]
fn compiled_rows_obey_name_scope_kind_text_uses_and_sorry_filters() {
    let rows = fixture();
    let db = database(&rows);
    let fake = FakeRepo { decls: rows };
    let names = |rows: Vec<Decl>| {
        let mut names: Vec<_> = rows.into_iter().map(|d| d.name).collect();
        names.sort();
        names
    };
    let queries = [
        Query { name: Some("*succ*".into()), ..Query::new() },
        Query { name: Some("Γ_eq".into()), ..Query::new() },
        Query { name: Some("γ*EQ".into()), ..Query::new() },
        Query { module: Some("SearchFixture".into()), ..Query::new() },
        Query { module: Some("searchfixture".into()), ..Query::new() },
        Query { module: Some("SearchFixtur".into()), ..Query::new() },
        Query { module: Some("SearchFixture%".into()), ..Query::new() },
        Query { source: Some(SourceId::new("fixture")), ..Query::new() },
        Query { source: Some(SourceId::new("missing")), ..Query::new() },
        Query { kind: vec![DeclKind::Theorem], no_sorry: true, ..Query::new() },
        Query { kind: vec![DeclKind::Def], ..Query::new() },
        Query { kind: vec![DeclKind::Instance], ..Query::new() },
        Query { uses: vec![DeclName::new("Nat.succ")], ..Query::new() },
        Query { uses: vec![DeclName::new(".succ")], ..Query::new() },
        Query {
            uses: vec![DeclName::new("Nat.succ"), DeclName::new("Option.some")],
            ..Query::new()
        },
        Query { text: vec!["symmetry".into()], ..Query::new() },
        Query { text: vec!["addition".into(), "symmetry".into()], ..Query::new() },
    ];
    for mut q in queries {
        q.limit = 100;
        let expected = names(fake.find(&q).unwrap());
        assert_eq!(names(db.find(&q).unwrap()), expected, "{q:?}");
        assert_eq!(DeclRepo::count(&db, &q).unwrap(), expected.len(), "{q:?}");
    }

    let mut q = Query { name: Some("admitted".into()), ..Query::new() };
    assert_eq!(db.find(&q).unwrap().len(), 1);
    q.no_sorry = true;
    assert!(db.find(&q).unwrap().is_empty());
}

#[test]
fn text_search_matches_names_whole_words_phrases_and_symbols_in_each_adapter() {
    let rows = fixture();
    let db = database(&rows);
    let raw = jsonl::JsonlRepo::from_decls(rows.clone());
    let fake = FakeRepo { decls: rows };
    let sorted = |rows: Vec<Decl>| {
        let mut names: Vec<_> = rows.into_iter().map(|d| d.name).collect();
        names.sort();
        names
    };
    for words in [
        vec!["documented"],
        vec!["SearchFixture.documented"],
        vec!["add", "comm"],
        vec!["addition", "symmetry"],
        vec!["addition and"],
        vec!["and addition"],
        vec!["sym"],
        vec!["ocumented"],
        vec!["Γ_eq"],
        vec!["↔"],
        vec!["≤", "Nat"],
        vec!["^"],
        vec!["\"symmetry\""],
    ] {
        let q = Query {
            text: words.iter().map(|s| s.to_string()).collect(),
            limit: 100,
            ..Query::new()
        };
        let expected = sorted(db.find(&q).unwrap());
        assert_eq!(sorted(raw.find(&q).unwrap()), expected, "JSONL: {words:?}");
        assert_eq!(sorted(fake.find(&q).unwrap()), expected, "domain: {words:?}");
        assert_eq!(DeclRepo::count(&db, &q).unwrap(), expected.len(), "{words:?}");
    }
    assert_eq!(
        db.find(&Query { text: vec!["documented".into()], ..Query::new() }).unwrap().len(),
        1
    );
    assert!(db.find(&Query { text: vec!["sym".into()], ..Query::new() }).unwrap().is_empty());
    assert!(!db.find(&Query { text: vec!["↔".into()], ..Query::new() }).unwrap().is_empty());
}

#[test]
fn unicode_text_search_uses_the_same_words_in_each_adapter() {
    let documents = [
        "café",
        "cafe",
        "CAFÉ",
        "e\u{301}x",
        "e x",
        "ς",
        "σ",
        "ẞ",
        "ß",
        "\u{e000}word",
        "word",
        "a²b",
        "a b",
    ];
    let rows: Vec<_> = documents
        .iter()
        .enumerate()
        .map(|(i, text)| {
            let mut row = Decl::stub(&format!("Corpus.row{i}"), "fixture", "Corpus");
            row.doc = Some((*text).into());
            row
        })
        .collect();
    let db = database(&rows);
    let raw = jsonl::JsonlRepo::from_decls(rows.clone());
    let fake = FakeRepo { decls: rows };
    let sorted = |rows: Vec<Decl>| {
        let mut names: Vec<_> = rows.into_iter().map(|d| d.name).collect();
        names.sort();
        names
    };
    for text in documents {
        let q = Query { text: vec![text.into()], limit: 100, ..Query::new() };
        let expected = sorted(fake.find(&q).unwrap());
        assert_eq!(sorted(raw.find(&q).unwrap()), expected, "JSONL: {text}");
        assert_eq!(sorted(db.find(&q).unwrap()), expected, "SQLite: {text}");
        assert_eq!(DeclRepo::count(&db, &q).unwrap(), expected.len(), "count: {text}");
    }
}

#[test]
fn combined_shape_filters_and_counts_agree_with_the_domain() {
    let rows = fixture();
    let db = database(&rows);
    let fake = FakeRepo { decls: rows };
    let sorted = |rows: Vec<Decl>| {
        let mut names: Vec<_> = rows.into_iter().map(|d| d.name).collect();
        names.sort();
        names
    };
    for &(written, _) in CASES {
        for kind in [Vec::new(), vec![DeclKind::Theorem], vec![DeclKind::Instance]] {
            for no_sorry in [false, true] {
                let q = Query {
                    kind: kind.clone(),
                    no_sorry,
                    limit: 100,
                    ..pattern::parse(written).query
                };
                let expected = sorted(fake.find(&q).unwrap());
                assert_eq!(sorted(db.find(&q).unwrap()), expected, "{written}: {q:?}");
                assert_eq!(DeclRepo::count(&db, &q).unwrap(), expected.len(), "{written}: {q:?}");
            }
        }
    }
}

#[test]
fn the_cli_searches_the_compiled_corpus_and_reports_invalid_queries() {
    let dir = TempDir::new("search-cli");
    dir.write("raw/fixture.jsonl", include_str!("fixtures/search.jsonl"));
    dir.write("SearchFixture.lean", include_str!("fixtures/SearchFixture.lean"));
    dir.write(
        "discrtree.toml",
        r#"
[project]
namespace = "SearchFixture"
src = "."
imports = "SearchFixture.lean"
vendor = "Vendor"
[index]
db = "index.db"
raw = "raw"
[[source]]
name = "fixture"
kind = "local"
path = "."
root = "SearchFixture"
"#,
    );
    let run = |args: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_dt")).args(args).current_dir(dir.path()).output().unwrap()
    };
    let output = run(&["index"]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    for (args, expected) in [
        (vec!["find", "(Nat.succ _ = _ + 1)", "--name", "succ_add"], "SearchFixture.succ_add"),
        (vec!["find", "¬ Nat.succ _ = 0"], "SearchFixture.not_succ_zero"),
        (vec!["find", "∃ n : Nat, Nat.succ n = 1"], "SearchFixture.exists_succ"),
        (
            vec!["find", "SearchFixture.TypePred (Nat → Nat)", "--kind", "theorem"],
            "SearchFixture.function_type",
        ),
        (vec!["find", "--name", "Γ_eq"], "SearchFixture.Γ_eq"),
        (vec!["find", "--name", "documented", "--text", "symmetry"], "SearchFixture.documented"),
    ] {
        let output = run(&args);
        assert!(output.status.success(), "{args:?}: {}", String::from_utf8_lossy(&output.stderr));
        let text = String::from_utf8(output.stdout).unwrap();
        assert!(text.contains(expected), "{args:?}: {text}");
    }
    let output = run(&["find", "--name", "admitted", "--no-sorry"]);
    assert!(output.status.success());
    assert!(!String::from_utf8(output.stdout).unwrap().contains("SearchFixture.admitted"));
    let output = run(&["find", "_ ∆ _ = _"]);
    let text = String::from_utf8(output.stdout).unwrap();
    assert!(text.contains('∆') && !text.contains("SearchFixture."), "{text}");
    let output = run(&["find", "--name", "succ_add", "--source", "Fixture"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("no source `Fixture`"));
    let output = run(&["find", "--name", "succ_add", "--limit", &usize::MAX.to_string()]);
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).contains("SearchFixture.succ_add"));
}

#[test]
fn module_prefixes_are_literal_and_case_sensitive_in_search_and_reverse_dependencies() {
    let mut rows = Vec::new();
    for module in [
        "Corpus",
        "Corpus.Child",
        "corpus.Child",
        "CorpusExtra.Child",
        "Corpus_A",
        "Corpus_A.Child",
        "CorpusXA.Child",
        "Corpus%A.Child",
        "Corpus?A.Child",
        "Corpus*A.Child",
        "Corpus[A.Child",
        "Corpus]A.Child",
    ] {
        let mut row =
            fixture().into_iter().find(|d| d.name.as_str() == "SearchFixture.option_map").unwrap();
        row.name = DeclName::new(format!("{module}.fixture"));
        row.module = ModuleName::new(module);
        rows.push(row);
    }
    let db = database(&rows);
    let fake = FakeRepo { decls: rows };
    let sorted = |rows: Vec<Decl>| {
        let mut names: Vec<_> = rows.into_iter().map(|d| d.name).collect();
        names.sort();
        names
    };
    for module in [
        "", "Corpus", "corpus", "Corpus_A", "Corpus%A", "Corpus?A", "Corpus*A", "Corpus[A",
        "Corpus]A", "Corpus_", "Corpus.",
    ] {
        let q = Query { module: Some(module.into()), limit: 100, ..Query::new() };
        let expected = sorted(fake.find(&q).unwrap());
        assert_eq!(sorted(db.find(&q).unwrap()), expected, "--in {module}");
        assert_eq!(DeclRepo::count(&db, &q).unwrap(), expected.len(), "--in {module}");
        let root = DeclName::new("Nat.succ");
        let real = sorted(db.used_by(&root, &q).unwrap().into_iter().map(|m| m.decl).collect());
        let expected =
            sorted(fake.used_by(&root, &q).unwrap().into_iter().map(|m| m.decl).collect());
        assert_eq!(real, expected, "rdeps --in {module}");
    }
}

/// Optional end-to-end check of the *current* dump script against real Lean.
/// The regular tests consume the committed dump and require no Lean install.
/// Run `cargo test --test lean_search live_lean_search -- --ignored`; set
/// DISCRTREE_LEAN to override the pinned compiler, and
/// DISCRTREE_UPDATE_FIXTURES=1 to regenerate the committed JSONL.
#[test]
#[ignore = "requires the Lean toolchain in tests/fixtures/lean-toolchain"]
fn live_lean_search() {
    let dir = TempDir::new("live-search");
    dir.write("lean-toolchain", include_str!("fixtures/lean-toolchain"));
    dir.write("SearchFixture.lean", include_str!("fixtures/SearchFixture.lean"));
    let lean = std::env::var_os("DISCRTREE_LEAN").unwrap_or_else(|| "lean".into());
    let compiled = Command::new(&lean)
        .args(["-o", "SearchFixture.olean", "SearchFixture.lean"])
        .current_dir(dir.path())
        .output()
        .expect("run Lean to compile the search fixture");
    assert!(
        compiled.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&compiled.stdout),
        String::from_utf8_lossy(&compiled.stderr)
    );
    let script = dir.write("Dump.lean", &splice_imports(DUMP_LEAN, "SearchFixture").unwrap());
    let dump = dir.path().join("search.jsonl");
    let dumped = Command::new(&lean)
        .arg(script)
        .current_dir(dir.path())
        .env("LEAN_PATH", dir.path())
        .env("DISCRTREE_SOURCE", "fixture")
        .env("DISCRTREE_MODULES", "SearchFixture")
        .env("DISCRTREE_OUT", &dump)
        .env("DISCRTREE_DEPS", "1")
        .env("DISCRTREE_JOBS", "2")
        .output()
        .expect("run the real dump script");
    assert!(
        dumped.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&dumped.stdout),
        String::from_utf8_lossy(&dumped.stderr)
    );
    let mut rows = jsonl::read(&dump).unwrap();
    rows.sort_by(|a, b| a.name.cmp(&b.name));
    exercise(&database(&rows));
    if std::env::var_os("DISCRTREE_UPDATE_FIXTURES").is_some() {
        let text: String = rows
            .iter()
            .map(|d| format!("{}\n", serde_json::to_string(&Row::from(d)).unwrap()))
            .collect();
        std::fs::write(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/search.jsonl"),
            text,
        )
        .unwrap();
    } else {
        let golden = fixture();
        assert_eq!(rows.len(), golden.len(), "the compiler changed the fixture's declaration set");
        for (actual, expected) in rows.iter().zip(golden) {
            assert_eq!(actual.name, expected.name);
            assert_eq!(actual.shape, expected.shape, "{}", actual.name);
            assert_eq!(actual.term, expected.term, "{}", actual.name);
            assert_eq!(actual.consts, expected.consts, "{}", actual.name);
            assert_eq!(actual.kind, expected.kind, "{}", actual.name);
            assert_eq!(actual.has_sorry, expected.has_sorry, "{}", actual.name);
            assert_eq!(actual.unfolds, expected.unfolds, "{}", actual.name);
        }
    }
}

#[test]
#[ignore = "requires the Lean toolchain in tests/fixtures/lean-toolchain"]
fn live_standard_library_search() {
    live_core_search(
        core_fixture(),
        "Init.Data.Nat,Init.Data.List,Init.Data.Option,Init.Data.Prod",
        "core-search.jsonl",
        "DISCRTREE_UPDATE_CORE_FIXTURES",
        false,
    );
}

#[test]
#[ignore = "requires the Lean toolchain in tests/fixtures/lean-toolchain"]
fn live_extended_standard_library_search() {
    live_core_search(
        data_fixture(),
        "Init.Data",
        "data-search.jsonl",
        "DISCRTREE_UPDATE_DATA_FIXTURES",
        true,
    );
}

fn live_core_search(
    golden: Vec<Decl>,
    modules: &str,
    file: &str,
    update: &str,
    module_scope: bool,
) {
    let dir = TempDir::new("live-core-search");
    dir.write("lean-toolchain", include_str!("fixtures/lean-toolchain"));
    let script = dir.write("Dump.lean", &splice_imports(DUMP_LEAN, "Lean").unwrap());
    let dump = dir.path().join("core.jsonl");
    let lean = std::env::var_os("DISCRTREE_LEAN").unwrap_or_else(|| "lean".into());
    let output = Command::new(lean)
        .arg(script)
        .current_dir(dir.path())
        .env("DISCRTREE_SOURCE", "core")
        .env("DISCRTREE_MODULES", modules)
        .env("DISCRTREE_OUT", &dump)
        .env("DISCRTREE_DEPS", "0")
        .env("DISCRTREE_JOBS", "2")
        .output()
        .expect("dump the installed standard library with Lean");
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let rows = jsonl::read(&dump).unwrap();
    let mut selected: Vec<Decl> =
        rows.iter().filter(|d| golden.iter().any(|g| g.name == d.name)).cloned().collect();
    selected.sort_by(|a, b| a.name.cmp(&b.name));
    assert_eq!(selected.len(), golden.len(), "the compiler changed the regression declaration set");
    let supported: Vec<Decl> = rows
        .iter()
        .filter(|d| {
            d.kind == DeclKind::Theorem
                && d.shaped()
                && !d.is_generated()
                && pattern::parse(&d.ty).unknown.is_empty()
        })
        .cloned()
        .collect();
    let minimum = if module_scope { 20_000 } else { 4_000 };
    assert!(supported.len() > minimum, "the standard-library search corpus unexpectedly shrank");
    eprintln!("checking {} printed standard-library statements", supported.len());
    exercise_core_scoped(&database(&rows), &supported, module_scope);
    if std::env::var_os(update).is_some() {
        jsonl::write(
            &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(file),
            &selected,
        )
        .unwrap();
    } else {
        for (actual, expected) in selected.iter().zip(golden) {
            assert_eq!(actual.name, expected.name);
            assert_eq!(actual.ty, expected.ty, "{}", actual.name);
            assert_eq!(actual.shape, expected.shape, "{}", actual.name);
            assert_eq!(actual.consts, expected.consts, "{}", actual.name);
            assert_eq!(actual.kind, expected.kind, "{}", actual.name);
        }
    }
}
