use discrtree::domain::decl::ArgHead;
use discrtree::domain::name::DeclName;
use discrtree::domain::pattern;

#[test]
fn empty_groups_are_prefix_arguments_in_their_written_position() {
    let p = pattern::parse("List.Lex r [] (a :: l)");
    assert_eq!(
        p.query.shape.args,
        [ArgHead::Any, ArgHead::parse("List.nil"), ArgHead::parse("List.cons")]
    );
    assert!(p.query.uses.is_empty(), "{:?}", p.query);
    for text in ["SearchFixture.TypePred ()", "SearchFixture.TypePred {}"] {
        let p = pattern::parse(text);
        assert_eq!(p.query.shape.args.len(), 1, "{text}");
    }
}

#[test]
fn quoted_literals_do_not_contain_search_operators_or_binders() {
    let p = pattern::parse("\"Nat.succ + ∀ → [id]\" = \"Nat.succ + ∀ → [id]\"");
    assert!(p.unknown.is_empty(), "{:?}", p.unknown);
    assert_eq!(p.query.shape.concl, Some("Eq".into()));
    assert_eq!(p.query.shape.args, [ArgHead::Any, ArgHead::Any]);
    assert!(p.query.uses.is_empty(), "{:?}", p.query);
    for text in ["'a' = _", "'→' = _", "'\\'' = _", "'\\n' = _"] {
        let p = pattern::parse(text);
        assert!(p.unknown.is_empty(), "{text}: {:?}", p.unknown);
        assert_eq!(p.query.shape.concl, Some("Eq".into()), "{text}");
        assert_eq!(p.query.shape.args[0], ArgHead::parse("Char.ofNat"), "{text}");
    }
}

#[test]
fn array_literals_keep_their_own_head_when_nested_or_indexed() {
    for text in
        ["#[] = _", "#[n, m] = _", "#[#[n], #[]] = _", "#[[n], [m]] = _", "#[xs[0]?, xs[1]!] = _"]
    {
        let p = pattern::parse(text);
        assert!(p.unknown.is_empty(), "{text}: {:?}", p.unknown);
        assert_eq!(p.query.shape.args[0], ArgHead::parse("List.toArray"), "{text}");
    }
    for (text, head) in [("#[n].size = _", ".size"), ("#[n][i]? = _", "GetElem?.getElem?")] {
        let p = pattern::parse(text);
        assert_eq!(p.query.shape.args[0], ArgHead::parse(head), "{text}");
        assert!(p.query.uses.contains(&"List.toArray".into()), "{text}");
    }
    for text in ["#[n", "#[[n]"] {
        let p = pattern::parse(&format!("{text} = _"));
        assert!(!p.unknown.is_empty(), "{text}: {:?}", p.query);
    }
}

#[test]
fn scientific_and_hexadecimal_literals_have_the_compilers_heads() {
    for text in ["1.25 = _", "1e3 = _", "1.25e-3 = _", "125e1 = _"] {
        let p = pattern::parse(text);
        assert!(p.unknown.is_empty(), "{text}: {:?}", p.unknown);
        assert_eq!(p.query.shape.args[0], ArgHead::parse("OfScientific.ofScientific"), "{text}");
        assert!(!p.query.uses.contains(&"HSub.hSub".into()), "{text}");
    }
    let p = pattern::parse("0xff = 255");
    assert!(p.unknown.is_empty(), "{:?}", p.unknown);
    assert_eq!(p.query.shape.args, [ArgHead::parse("OfNat.ofNat"), ArgHead::parse("OfNat.ofNat")]);
}

#[test]
fn numerals_can_receive_index_notation() {
    for (text, head) in [
        ("0[i] = 0", "GetElem.getElem"),
        ("0[i]? = none", "GetElem?.getElem?"),
        ("0[i]! = 0", "GetElem?.getElem!"),
    ] {
        let parsed = pattern::parse(text);
        assert_eq!(parsed.query.shape.args[0], ArgHead::parse(head), "{text}");
        assert!(!parsed.query.uses.contains(&"List.cons".into()), "{text}");
    }
}

#[test]
fn top_level_lets_are_stripped_with_universal_binders() {
    for text in [
        "let id := Nat.succ 0; id = id",
        "∀ n : Nat, let id := n + 1; ∀ m : Nat, id = id",
        "let Carrier := Nat; ∀ n : Carrier, n = n",
        "have id := Nat.succ 0; id = id",
    ] {
        let parsed = pattern::parse(text);
        assert_eq!(parsed.query.shape.concl, Some("Eq".into()), "{text}");
        assert_eq!(parsed.query.shape.args, vec![ArgHead::Any, ArgHead::Any], "{text}");
        assert!(
            !parsed.query.uses.iter().any(|n| ["let", "id", "Carrier"].contains(&n.as_str())),
            "{text}: {:?}",
            parsed.query
        );
    }
    let parsed = pattern::parse("(let id := Nat.succ 0; id = id) ∧ id _ = _");
    assert!(parsed.query.uses.contains(&"id".into()));
}

#[test]
fn polymorphic_ranges_preserve_bounds_and_postfix_fields() {
    for (range, head) in [
        ("m...n", "Std.Rco.mk"),
        ("m...<n", "Std.Rco.mk"),
        ("m...=n", "Std.Rcc.mk"),
        ("m...*", "Std.Rci.mk"),
        ("m<...n", "Std.Roo.mk"),
        ("m<...<n", "Std.Roo.mk"),
        ("m<...=n", "Std.Roc.mk"),
        ("m<...*", "Std.Roi.mk"),
        ("*...n", "Std.Rio.mk"),
        ("*...<n", "Std.Rio.mk"),
        ("*...=n", "Std.Ric.mk"),
        ("*...*", "Std.Rii.mk"),
    ] {
        let text = format!("({range}) = ({range})");
        let parsed = pattern::parse(&text);
        assert_eq!(
            parsed.query.shape.args,
            vec![ArgHead::parse(head), ArgHead::parse(head)],
            "{text}"
        );
        assert!(parsed.unknown.is_empty(), "{text}: {:?}", parsed.unknown);
    }
    let parsed = pattern::parse("((m + 1)...n).toList = (m...n + 1).toList");
    assert_eq!(parsed.query.shape.args, vec![ArgHead::parse(".toList"), ArgHead::parse(".toList")]);
    assert!(parsed.query.uses.contains(&"Std.Rco.mk".into()));
    assert!(!parsed.query.uses.contains(&".n".into()));
}

#[test]
fn anonymous_constructors_and_record_labels_do_not_guess_constant_heads() {
    for text in
        ["⟨0, proof⟩ = _", "⟨0, ⋯⟩ = _", "{ byteIdx := n } = _", "{ toFin := Fin.ofNat _ _ } = _"]
    {
        let parsed = pattern::parse(text);
        assert_eq!(parsed.query.shape.args[0], ArgHead::Any, "{text}");
        assert!(!parsed.query.uses.contains(&"byteIdx".into()), "{text}");
        assert!(!parsed.query.uses.contains(&"toFin".into()), "{text}");
        assert!(parsed.unknown.is_empty(), "{text}: {:?}", parsed.unknown);
    }
    assert!(
        pattern::parse("{ toFin := Fin.ofNat _ _ } = _").query.uses.contains(&"Fin.ofNat".into())
    );
}

#[test]
fn negative_operands_do_not_require_subtraction() {
    for text in ["a ||| -1 = -1", "x + -1 = -1", "x &&& -1 = x", "x = if p then -1 else 0"] {
        let parsed = pattern::parse(text);
        assert!(!parsed.query.uses.contains(&"HSub.hSub".into()), "{text}: {:?}", parsed.query);
    }
}

#[test]
fn applicative_operators_are_single_tokens() {
    for (operator, head) in [
        ("<*>", "Seq.seq"),
        ("<*", "SeqLeft.seqLeft"),
        ("*>", "SeqRight.seqRight"),
        (">>", "HAndThen.hAndThen"),
        ("<$>", "Functor.map"),
    ] {
        let text = format!("(a {operator} b) = a {operator} b");
        let parsed = pattern::parse(&text);
        assert_eq!(
            parsed.query.shape.args,
            vec![ArgHead::parse(head), ArgHead::parse(head)],
            "{text}"
        );
        assert!(parsed.query.uses.is_empty(), "{text}: {:?}", parsed.query);
    }
}

#[test]
fn iff_contains_unparenthesized_implications() {
    for (text, args) in [
        ("p → q ↔ r", vec![ArgHead::Any, ArgHead::Any]),
        ("p ↔ q → r", vec![ArgHead::Any, ArgHead::Any]),
        ("_ = _ → _ = _ ↔ _ = _", vec![ArgHead::Any, ArgHead::parse("Eq")]),
        ("_ = _ ↔ _ = _ → _ = _", vec![ArgHead::parse("Eq"), ArgHead::Any]),
    ] {
        let parsed = pattern::parse(text);
        assert_eq!(parsed.hypotheses, 0, "{text}");
        assert_eq!(parsed.query.shape.concl, Some("Iff".into()), "{text}");
        assert_eq!(parsed.query.shape.args, args, "{text}");
    }
    let parsed = pattern::parse("(_ = _ ↔ _ = _) → _ = _");
    assert_eq!(parsed.hypotheses, 1);
    assert_eq!(parsed.query.shape.concl, Some("Eq".into()));
}

#[test]
fn coercions_do_not_inherit_the_heads_of_their_operands() {
    for text in ["↑0 = 0", "↑x.toNat = 0", "↑(Nat.succ _) = 0", "⇑f = 0"] {
        let parsed = pattern::parse(text);
        assert_eq!(parsed.query.shape.args[0], ArgHead::Any, "{text}");
        assert!(parsed.unknown.is_empty(), "{text}");
    }
    assert!(pattern::parse("↑(Nat.succ _) = 0").query.uses.contains(&"Nat.succ".into()));
    assert_eq!(pattern::parse("↑n + 1 = 0").query.shape.args[0], ArgHead::parse("HAdd.hAdd"));
}

#[test]
fn grouping_an_entire_formula_preserves_its_query() {
    for pattern in [
        "Nat.succ _ = _",
        "_ ≤ Nat.succ _",
        "_ = _ ↔ _ = _ ∧ _ = _",
        "Nat.succ _ = _ → Nat.succ _ = _",
        "∀ n : Nat, Nat.succ n = n + 1",
    ] {
        let plain = pattern::parse(pattern);
        for grouped in [format!("({pattern})"), format!("(({pattern}))")] {
            let parsed = pattern::parse(&grouped);
            assert_eq!(parsed.query, plain.query, "{grouped}");
            assert_eq!(parsed.hypotheses, plain.hypotheses, "{grouped}");
            assert_eq!(parsed.query.powers, plain.query.powers, "{grouped}");
            assert_eq!(parsed.query.inside, plain.query.inside, "{grouped}");
        }
    }
}

#[test]
fn binding_a_variable_preserves_repeated_factors_in_powers() {
    let plain = pattern::parse("x * x = x ^ 2").query.powers;
    for pattern in ["∀ x : Nat, x * x = x ^ 2", "∀ id : Nat, id * id = id ^ 2"] {
        assert_eq!(pattern::parse(pattern).query.powers, plain, "{pattern}");
    }
}

#[test]
fn sort_keywords_are_not_constant_names() {
    for pattern in [
        "SearchFixture.TypePred Prop",
        "SearchFixture.TypePred (Type _)",
        "SearchFixture.TypePred (Sort _)",
    ] {
        let p = pattern::parse(pattern);
        assert_eq!(p.query.shape.args, [ArgHead::Any], "{pattern}");
        assert!(p.query.uses.is_empty(), "{pattern}: {:?}", p.query.uses);
    }
}

#[test]
fn a_bound_name_cannot_hide_a_constant_outside_its_scope() {
    let p = pattern::parse("(∀ id : Nat, id = id) ↔ id _ = _");
    assert!(p.query.uses.contains(&DeclName::new("id")), "{:?}", p.query);
    assert!(p.variables.contains(&"id".into()));
    let p = pattern::parse("(∀ Nat : Type, ∀ n : Nat, n = n) ∧ Nat.succ 0 = 1");
    assert_eq!(p.query.shape.args, [ArgHead::Any, ArgHead::parse("Eq")]);
    assert_eq!(p.query.uses, [DeclName::new("Nat.succ")]);
}

#[test]
fn arrows_in_arguments_and_binder_types_are_not_hypotheses() {
    for pattern in [
        "SearchFixture.TypePred (Nat → Nat)",
        "SearchFixture.TypePred ((Nat → Nat) → Nat)",
        "∀ (f : Nat → Nat) (n : Nat), f n = f n",
        "∀ {f : Nat → Nat}, f _ = f _",
        "∀ [inst : Inhabited (Nat → Nat)], Nat.succ _ = _",
    ] {
        assert_eq!(pattern::parse(pattern).hypotheses, 0, "{pattern}");
    }
    let p = pattern::parse("SearchFixture.TypePred (Nat → Nat)");
    assert_eq!(p.query.shape.concl, Some(DeclName::new("SearchFixture.TypePred")));
    assert_eq!(p.query.shape.args, [ArgHead::Any]);
}

#[test]
fn a_parenthesized_implication_keeps_its_conclusion() {
    let p = pattern::parse("Nat.succ _ = _ → (_ = _ → Nat.succ _ = _)");
    assert_eq!(p.hypotheses, 2);
    assert_eq!(p.query, pattern::parse("Nat.succ _ = _ → _ = _ → Nat.succ _ = _").query);
}

#[test]
fn logical_prefixes_are_the_outer_head_of_the_formula() {
    for (pattern, head, args) in [
        ("¬ Nat.succ _ = 0", "Not", vec!["Eq"]),
        ("¬ (Nat.succ _ = 0)", "Not", vec!["Eq"]),
        ("¬ (_ ∈ _) ↔ _ ∉ _", "Iff", vec!["Not", "Not"]),
        ("∃ n : Nat, Nat.succ n = 1", "Exists", vec![]),
        ("∃ n : Nat, n = 0 → Nat.succ n = 1", "Exists", vec![]),
        ("¬ ∃ n : Nat, n = 0 ∧ (n = 0 → False)", "Not", vec!["Exists"]),
        ("_ ∧ ∃ n : Nat, n = 0 ∨ n = 1", "And", vec!["_", "Exists"]),
        ("_ ∧ ∀ n : Nat, n = 0 → n = 0", "And", vec!["_", "_"]),
        ("¬ (∃ n : Nat, Nat.succ n = 0)", "Not", vec!["Exists"]),
        ("Nat.succ _ + _", "HAdd.hAdd", vec![]),
    ] {
        let p = pattern::parse(pattern);
        assert!(p.unknown.is_empty(), "{pattern}: {:?}", p.unknown);
        assert_eq!(p.query.shape.concl, Some(DeclName::new(head)), "{pattern}");
        let args: Vec<_> = args.into_iter().map(ArgHead::parse).collect();
        assert_eq!(p.query.shape.args, args, "{pattern}");
    }
}

#[test]
fn quantifier_bodies_do_not_become_outer_hypotheses() {
    for pattern in [
        "∃ n : Nat, n = 0 → Nat.succ n = 1",
        "¬ ∃ n : Nat, n = 0 ∧ (n = 0 → False)",
        "_ ∧ ∀ n : Nat, n = 0 → n = 0",
    ] {
        assert_eq!(pattern::parse(pattern).hypotheses, 0, "{pattern}");
    }
    assert_eq!(pattern::parse("∀ n : Nat, n = 0 → n = 0").hypotheses, 1);
}

#[test]
fn explicit_binders_win_over_constant_names() {
    for pattern in [
        "∀ id : Nat, id + id = id + id",
        "forall id : Nat, id + id = id + id",
        "∀ (Nat : Type) (n : Nat), n = n",
        "∀ (function : Nat → Nat) (id : Nat), function id = function id",
    ] {
        let p = pattern::parse(pattern);
        assert!(p.query.uses.is_empty(), "{pattern}: {:?}", p.query.uses);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")), "{pattern}");
    }
}

#[test]
fn compound_operators_keep_their_actual_lean_heads() {
    for (written, head) in [
        ("==", "BEq.beq"),
        ("&&", "Bool.and"),
        ("||", "Bool.or"),
        ("^^", "Bool.xor"),
        ("<<<", "HShiftLeft.hShiftLeft"),
        (">>>", "HShiftRight.hShiftRight"),
        ("&&&", "HAnd.hAnd"),
        ("|||", "HOr.hOr"),
        ("^^^", "HXor.hXor"),
    ] {
        let p = pattern::parse(&format!("(_ {written} _) = (_ {written} _)"));
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")), "{written}");
        assert_eq!(p.query.shape.args, [ArgHead::parse(head), ArgHead::parse(head)], "{written}");
        assert!(p.unknown.is_empty(), "{written}: {:?}", p.unknown);
    }
}

#[test]
fn prefix_operators_on_the_right_do_not_replace_the_outer_relation() {
    for (written, head) in [("¬", "Not"), ("!", "Bool.not"), ("~~~", "Complement.complement")] {
        let p = pattern::parse(&format!("({written} _) = {written} _"));
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")), "{written}");
        assert_eq!(p.query.shape.args, [ArgHead::parse(head), ArgHead::parse(head)], "{written}");
    }
    for (written, head) in [
        ("¬ _ = _", "Not"),
        ("!_ == _", "Bool.not"),
        ("-x ^ 2", "Neg.neg"),
        ("-x * x", "HMul.hMul"),
        ("!p && q", "Bool.and"),
    ] {
        assert_eq!(
            pattern::parse(written).query.shape.concl,
            Some(DeclName::new(head)),
            "{written}"
        );
    }
}

#[test]
fn list_literals_use_constructor_heads_instead_of_their_elements() {
    for (written, head) in [("[]", "List.nil"), ("[0]", "List.cons"), ("[_, _]", "List.cons")] {
        let p = pattern::parse(&format!("{written} = _"));
        assert_eq!(p.query.shape.args, [ArgHead::parse(head), ArgHead::Any], "{written}");
    }
    let p = pattern::parse("List.length [_, _] = 2");
    assert!(p.query.uses.contains(&DeclName::new("List.cons")), "{:?}", p.query);
    for written in ["[_, _].length = 2", "[].length = 0"] {
        assert_eq!(
            pattern::parse(written).query.shape.args[0],
            ArgHead::parse(".length"),
            "{written}"
        );
    }
    assert_eq!(
        pattern::parse("[] ++ [] = _").query.shape.args[0],
        ArgHead::parse("HAppend.hAppend")
    );
}

#[test]
fn conditional_bodies_do_not_become_outer_operators() {
    for (written, heads) in [
        ("_ = if _ ≤ _ then _ + _ else _ * _", ["_", "ite"]),
        ("(if _ ≤ _ then _ + _ else _ * _) = _", ["ite", "_"]),
        ("_ = if _ then _ else if _ then _ else _", ["_", "ite"]),
        ("_ + (if _ ≤ _ then 1 else 0) = _", ["HAdd.hAdd", "_"]),
    ] {
        let p = pattern::parse(written);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")), "{written}");
        assert_eq!(p.query.shape.args, heads.map(ArgHead::parse), "{written}");
        assert!(!p.query.uses.iter().any(|n| ["if", "then", "else"].contains(&n.as_str())));
    }
}

#[test]
fn subtype_syntax_is_not_division_and_its_binder_is_scoped() {
    let p = pattern::parse("SearchFixture.TypePred { id : Nat // id = id }");
    assert!(p.unknown.is_empty());
    assert_eq!(p.query.shape.args, [ArgHead::parse("Subtype")]);
    assert!(!p.query.uses.contains(&DeclName::new("HDiv.hDiv")));
    assert!(!p.query.uses.contains(&DeclName::new("id")));
    let p = pattern::parse("SearchFixture.TypePred { id : Nat // id = id } ∧ id _ = _");
    assert!(p.query.uses.contains(&DeclName::new("id")));
}

#[test]
fn dependent_binder_types_refer_to_the_previously_bound_variable() {
    let p = pattern::parse("∃ (Carrier : Type) (value : Carrier), True");
    assert_eq!(p.query.shape.concl, Some(DeclName::new("Exists")));
    assert_eq!(p.query.uses, [DeclName::new("True")]);
}

#[test]
fn membership_arguments_follow_leans_container_then_element_order() {
    let p = pattern::parse("Nat.succ _ ∈ _ :: _");
    assert_eq!(p.query.shape.args, [ArgHead::parse("List.cons"), ArgHead::parse("Nat.succ")]);
    let p = pattern::parse("x ^ 2 ∈ _");
    assert_eq!(p.query.powers[0].0, 1, "the power belongs to the element argument");
    assert_eq!(p.query.shape.args, [ArgHead::Any, ArgHead::parse("HPow.hPow")]);
}

#[test]
fn heterogeneous_equality_includes_both_operands_implicit_types() {
    let p = pattern::parse("Nat.succ _ ≍ Nat.succ _");
    assert_eq!(
        p.query.shape.args,
        [ArgHead::Any, ArgHead::parse("Nat.succ"), ArgHead::Any, ArgHead::parse("Nat.succ")]
    );
    assert!(p.query.shape.include_implicit);
    let p = pattern::parse("_ ≍ x ^ 2");
    assert_eq!(p.query.powers[0].0, 3);
}

#[test]
fn an_explicit_application_flag_belongs_to_its_own_conclusion() {
    for text in ["@Eq Nat _ _", "(@Eq Nat _ _)", "∀ n : Nat, @Eq Nat n n"] {
        assert!(pattern::parse(text).query.shape.include_implicit, "{text}");
    }
    for text in ["Eq Nat _", "@Nat.succ n = n + 1", "Not (@Eq Nat n n)"] {
        assert!(!pattern::parse(text).query.shape.include_implicit, "{text}");
    }
}

#[test]
fn boolean_not_equals_and_standalone_ascii_inequality_keep_their_readings() {
    assert_eq!(pattern::parse("Nat.succ _ != 0").query, pattern::parse("Nat.succ _ ≠ 0").query);
    for written in ["(_ != _) = true", "((_ != _)) = true", "(_ != _) = (_ != _)"] {
        let p = pattern::parse(written);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")), "{written}");
        assert_eq!(p.query.shape.args[0], ArgHead::parse("bne"), "{written}");
    }
}

#[test]
fn a_lambda_cannot_consume_a_tuple_tail_or_a_field_after_its_group() {
    let p = pattern::parse("(fun n => n, 0) = (_, _)");
    assert_eq!(p.query.shape.args, [ArgHead::parse("Prod.mk"), ArgHead::parse("Prod.mk")]);
    assert_eq!(p.lambdas, ["fun n => n"]);
    let p =
        pattern::parse("(List.map (fun n => match n with | 0 => 0 | n + 1 => n) _).reverse = _");
    assert_eq!(p.query.shape.args[0], ArgHead::parse(".reverse"));
    assert_eq!(p.query.uses, [DeclName::new("List.map")]);
}

#[test]
fn generated_proof_names_do_not_become_impossible_uses_conditions() {
    let p = pattern::parse("autoParam (_ = _) Nat.foo._auto_1 → Nat.succ _ = _");
    assert!(!p.query.uses.contains(&DeclName::new("Nat.foo._auto_1")));
    let p = pattern::parse("_ = [_ Nat.foo._proof_1]");
    assert!(!p.query.uses.contains(&DeclName::new("Nat.foo._proof_1")));
}
