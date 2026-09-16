//! The declaration. One row of the index, whichever corpus it came from.

use crate::domain::name::{DeclName, ModuleName};
use crate::domain::source::SourceId;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// 1-based, inclusive, as Lean reports declaration ranges.
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Span { start, end }
    }

    pub fn lines(&self) -> u32 {
        self.end.saturating_sub(self.start) + 1
    }

    /// Slice the lines of a file. Out-of-range spans yield what is there rather
    /// than failing: a stale index should degrade, not stop the tool.
    pub fn slice<'a>(&self, text: &'a str) -> Vec<&'a str> {
        text.lines()
            .skip(self.start.saturating_sub(1) as usize)
            .take(self.lines() as usize)
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclKind {
    Theorem,
    Def,
    Structure,
    Inductive,
    Axiom,
    Instance,
    Ctor,
    Other(String),
}

/// Every kind a dump writes: the seven Lean's own declaration commands come
/// to, and the three kernel ones a search can still land on.
pub const KINDS: &[&str] = &[
    "theorem",
    "def",
    "structure",
    "inductive",
    "axiom",
    "instance",
    "ctor",
    "opaque",
    "rec",
    "quot",
];

/// Commands that are not kinds of their own: Lean elaborates each into one of
/// [`KINDS`], and the index records what it became.
pub const ALIASES: &[(&str, &str)] =
    &[("lemma", "theorem"), ("abbrev", "def"), ("class", "structure")];

impl DeclKind {
    pub fn parse(s: &str) -> DeclKind {
        match s {
            "theorem" | "lemma" => DeclKind::Theorem,
            "def" | "abbrev" | "noncomputable def" => DeclKind::Def,
            "structure" | "class" => DeclKind::Structure,
            "inductive" => DeclKind::Inductive,
            "axiom" => DeclKind::Axiom,
            "instance" => DeclKind::Instance,
            "ctor" => DeclKind::Ctor,
            other => DeclKind::Other(other.to_string()),
        }
    }

    /// The kind a reader asked for by name, or `None` for a word that is not
    /// one. [`DeclKind::parse`] keeps any word, because a dump may carry a kind
    /// this build has not heard of; a flag has no such excuse, and a kind no
    /// row can have is a typo that would otherwise come back as `no match`.
    pub fn named(s: &str) -> Option<DeclKind> {
        (KINDS.contains(&s) || ALIASES.iter().any(|(a, _)| *a == s)).then(|| DeclKind::parse(s))
    }

    pub fn as_str(&self) -> &str {
        match self {
            DeclKind::Theorem => "theorem",
            DeclKind::Def => "def",
            DeclKind::Structure => "structure",
            DeclKind::Inductive => "inductive",
            DeclKind::Axiom => "axiom",
            DeclKind::Instance => "instance",
            DeclKind::Ctor => "ctor",
            DeclKind::Other(s) => s,
        }
    }

    /// Whether the declaration states something. `dt dup` only compares these.
    pub fn is_proposition(&self) -> bool {
        matches!(self, DeclKind::Theorem | DeclKind::Axiom)
    }
}

impl fmt::Display for DeclKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The head symbol of one argument of a conclusion. `Any` covers a variable, a
/// lambda, a literal — anything that is not an application of a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgHead {
    Named(DeclName),
    Any,
}

impl ArgHead {
    pub fn parse(s: &str) -> ArgHead {
        if s == "_" || s.is_empty() { ArgHead::Any } else { ArgHead::Named(DeclName::new(s)) }
    }

    pub fn as_str(&self) -> &str {
        match self {
            ArgHead::Named(n) => n.as_str(),
            ArgHead::Any => "_",
        }
    }

    /// A pattern argument matches a declaration argument if the pattern is `_`
    /// or the pattern's head names the declaration's. See [`DeclName::names`].
    pub fn matches(&self, other: &ArgHead) -> bool {
        match self {
            ArgHead::Any => true,
            ArgHead::Named(a) => matches!(other, ArgHead::Named(b) if a.names(b)),
        }
    }
}

/// The searchable skeleton of a statement: the conclusion's head symbol and the
/// head symbols of its arguments, one level deep.
///
/// This is what makes `_ ≤ Real.exp _` findable without knowing the name of the
/// lemma. Depth 2 and the bucketing that collapses `_ ≤ Real.exp _` with
/// `Real.exp _ ≥ _` is phase 5; this is the depth-1 half it builds on.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Shape {
    pub concl: Option<DeclName>,
    pub args: Vec<ArgHead>,
}

impl Shape {
    pub fn new(concl: Option<DeclName>, args: Vec<ArgHead>) -> Self {
        Shape { concl, args }
    }

    pub fn is_empty(&self) -> bool {
        self.concl.is_none() && self.args.is_empty()
    }

    /// Every constant the shape names: the conclusion head, then the argument
    /// heads that are not `_`.
    pub fn heads(&self) -> impl Iterator<Item = &DeclName> {
        self.concl.iter().chain(self.args.iter().filter_map(|a| match a {
            ArgHead::Named(n) => Some(n),
            ArgHead::Any => None,
        }))
    }

    /// Whether `self`, read as a pattern, matches `other`, read as a statement.
    ///
    /// Argument matching is positional but tolerant of arity: a pattern with
    /// fewer arguments than the statement matches a prefix, because `Eq` and
    /// the order classes carry leading type and instance arguments a user never
    /// writes. A pattern with *more* arguments cannot match.
    pub fn matches(&self, other: &Shape) -> bool {
        if let Some(c) = &self.concl
            && !other.concl.as_ref().is_some_and(|o| c.names(o))
        {
            return false;
        }
        if self.args.len() > other.args.len() {
            return false;
        }
        // Try every alignment of the pattern against the statement's arguments,
        // so `Real.exp _` matches `@LE.le ℝ inst (Real.exp x) y` without the
        // user having to write the instance arguments out.
        (0..=other.args.len() - self.args.len())
            .any(|off| self.args.iter().zip(&other.args[off..]).all(|(p, a)| p.matches(a)))
    }
}

/// What the type of a constructor's generated `elim` says, and a handwritten
/// `elim` does not: which constructor it is, by index.
pub const GENERATED_ELIM: &str = "ctorIdx = ";

/// One declaration, from any corpus.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
    pub name: DeclName,
    pub source: SourceId,
    pub module: ModuleName,
    pub kind: DeclKind,
    /// Pretty-printed type: elaborated for compiled sources, as written for
    /// text sources.
    pub ty: String,
    pub shape: Shape,
    /// Constants appearing in the type.
    pub consts: Vec<DeclName>,
    /// Dependencies. Exact (proof term) for compiled sources, approximated from
    /// imports and identifiers for text sources — [`Decl::elaborated`] says
    /// which, and every result line shows it.
    pub deps: Vec<DeclName>,
    pub doc: Option<String>,
    pub has_sorry: bool,
    pub span: Option<Span>,
    pub elaborated: bool,
}

impl Decl {
    /// A row with everything optional left out, for tests and for the scanner.
    pub fn stub(name: &str, source: &str, module: &str) -> Decl {
        Decl {
            name: DeclName::new(name),
            source: SourceId::new(source),
            module: ModuleName::new(module),
            kind: DeclKind::Theorem,
            ty: String::new(),
            shape: Shape::default(),
            consts: Vec::new(),
            deps: Vec::new(),
            doc: None,
            has_sorry: false,
            span: None,
            elaborated: true,
        }
    }

    /// Whether the compiler made this declaration up: what `inductive` and
    /// `@[congr]` leave behind next to the names a file actually declares.
    ///
    /// Kept in the index and hidden from `find` rather than dropped by the
    /// dump, so that an index written by an older dump benefits too and
    /// `--generated` can still ask. `elim` is also a name people choose --
    /// `Or.elim`, `False.elim` -- so only the one Lean makes for a constructor
    /// counts, and that one is told by its type, which is stated in terms of
    /// `ctorIdx`.
    pub fn is_generated(&self) -> bool {
        const GENERATED: &[&str] =
            &["ctorIdx", "ctorElim", "ctorElimType", "congr_simp", "ofNat_ctorIdx"];
        let name = self.name.as_str();
        GENERATED.contains(&self.name.base())
            || name.contains(".brecOn.")
            || (self.name.base() == "elim" && self.ty.contains(GENERATED_ELIM))
    }

    /// Whether the row carries enough structure for shape search.
    pub fn shaped(&self) -> bool {
        self.elaborated && self.shape.concl.is_some()
    }

    /// First non-empty line of the docstring, for one-line result rows.
    pub fn summary(&self) -> Option<&str> {
        self.doc.as_deref().and_then(|d| d.lines().find(|l| !l.trim().is_empty())).map(str::trim)
    }
}

/// The head symbols whose last component is `word`, commonest first, counted
/// over the rows whose type prints `word` as a name of its own. See
/// [`prints_bare`].
///
/// The rule for reading an unqualified pattern token, in one place: the
/// in-memory stores count over this, SQLite counts the same thing in SQL, and
/// the two agreeing is what makes either trustworthy. A row counts once however
/// often it has the head. Ties go to the shorter name and then alphabetically,
/// so the answer does not depend on what order the rows arrived in.
pub fn commonest_called<'a>(
    rows: impl Iterator<Item = (&'a str, Vec<&'a DeclName>)>,
    word: &str,
) -> Vec<DeclName> {
    let mut count: std::collections::HashMap<&DeclName, usize> = std::collections::HashMap::new();
    for (ty, heads) in rows {
        let mut called: Vec<&DeclName> = heads.into_iter().filter(|h| h.base() == word).collect();
        called.sort();
        called.dedup();
        if called.is_empty() || !prints_bare(ty, word) {
            continue;
        }
        for h in called {
            *count.entry(h).or_default() += 1;
        }
    }
    let mut ranked: Vec<(&DeclName, usize)> = count.into_iter().collect();
    ranked.sort_by(|(an, ac), (bn, bc)| {
        bc.cmp(ac).then(an.as_str().len().cmp(&bn.as_str().len())).then(an.cmp(bn))
    });
    ranked.into_iter().map(|(n, _)| n.clone()).collect()
}

/// Whether a printed type spells `word` without a namespace: somewhere as a
/// name of its own, nowhere after a `.`, and nowhere as a binder.
///
/// This is what tells a name Lean prints bare from a variable that happens to
/// share it. `export Bool (false)` makes every row with `Bool.false` in it say
/// `false`. `CategoryTheory.Discrete.as` heads 62 rows and not one of them says
/// `as` -- it is printed `X.as` -- so a pattern's `as ++ bs` is not about it.
/// A row that binds the word, `(val : α)` or `[inst : Monoid α]` or
/// `{ neg := y }`, says nothing about what the word names elsewhere, and is
/// where the rest of the false readings came from: `val` was `Units.val`
/// by three rows that name a hypothesis so.
pub fn prints_bare(ty: &str, word: &str) -> bool {
    let glued = |c: char| c.is_alphanumeric() || "_'".contains(c);
    let mut bare = false;
    for (at, _) in ty.match_indices(word) {
        let before = ty[..at].chars().next_back();
        let rest = &ty[at + word.len()..];
        if before.is_some_and(glued)
            || rest.chars().next().is_some_and(|c| glued(c) || "!?".contains(c))
        {
            continue;
        }
        if before == Some('.') || binds(rest) {
            return false;
        }
        bare = true;
    }
    bare
}

/// Whether what follows a word makes it a binder: more words, then ` :`.
/// `(as bs : List α)` binds both.
fn binds(mut rest: &str) -> bool {
    loop {
        let spaced = rest.trim_start();
        if spaced.len() == rest.len() {
            return false;
        }
        if spaced.starts_with(':') {
            return true;
        }
        let word = spaced.find(|c: char| c.is_whitespace() || "():,[]{}⦃⦄".contains(c));
        match word {
            Some(0) | None => return false,
            Some(end) => rest = &spaced[end..],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(concl: &str, args: &[&str]) -> Shape {
        Shape::new(Some(DeclName::new(concl)), args.iter().map(|a| ArgHead::parse(a)).collect())
    }

    #[test]
    fn what_the_compiler_writes_is_told_from_what_a_person_does() {
        let named = |n: &str, ty: &str| {
            let mut d = Decl::stub(n, "project", "M");
            d.ty = ty.into();
            d.is_generated()
        };
        assert!(named("Form.ctorIdx", ""));
        assert!(named("Form.and.congr_simp", ""));
        assert!(named("Form.brecOn.go", ""));
        assert!(named("Form.and.elim", "(t : Form) → t.ctorIdx = 3 → motive t"));
        assert!(!named("Or.elim", "(a ∨ b) → (a → c) → (b → c) → c"));
        assert!(!named("Form.sat_le", ""));
    }

    #[test]
    fn a_span_slices_inclusive_1_based_lines() {
        let text = "a\nb\nc\nd\n";
        assert_eq!(Span::new(2, 3).slice(text), vec!["b", "c"]);
        assert_eq!(Span::new(1, 1).lines(), 1);
        // A stale index pointing past the end yields what is there.
        assert_eq!(Span::new(3, 99).slice(text), vec!["c", "d"]);
    }

    #[test]
    fn a_pattern_matches_a_prefix_of_the_arguments() {
        // `Real.exp _ ≤ _` against `@LE.le ℝ inst (Real.exp x) y`.
        let stmt = shape("LE.le", &["_", "_", "Real.exp", "_"]);
        assert!(shape("LE.le", &["Real.exp", "_"]).matches(&stmt));
        assert!(shape("LE.le", &[]).matches(&stmt));
        assert!(!shape("LT.lt", &["Real.exp"]).matches(&stmt));
        assert!(!shape("LE.le", &["Finset.sum", "_"]).matches(&stmt));
    }

    /// `l.Nodup` and `xs.length = _` leave the namespace to the receiver's
    /// type, and match whichever one it is.
    #[test]
    fn a_field_in_a_pattern_matches_the_constant_in_any_namespace() {
        let stmt = shape("List.Nodup", &["_", "List.map"]);
        assert!(shape(".Nodup", &[".map"]).matches(&stmt));
        assert!(shape(".Nodup", &["_"]).matches(&stmt));
        assert!(!shape(".Nodu", &[]).matches(&stmt), "a whole component, not a suffix of one");
        assert!(!shape(".Nodup", &[".filter"]).matches(&stmt));
    }

    #[test]
    fn a_longer_pattern_cannot_match() {
        let stmt = shape("Eq", &["_", "Real.exp"]);
        assert!(!shape("Eq", &["_", "Real.exp", "_", "_"]).matches(&stmt));
    }

    #[test]
    fn an_empty_pattern_matches_anything() {
        assert!(Shape::default().matches(&shape("LE.le", &["Real.exp"])));
    }

    #[test]
    fn kinds_round_trip_and_unknown_ones_survive() {
        assert_eq!(DeclKind::parse("lemma"), DeclKind::Theorem);
        assert_eq!(DeclKind::parse("class"), DeclKind::Structure);
        assert_eq!(DeclKind::parse("opaque").as_str(), "opaque");
        assert!(DeclKind::Theorem.is_proposition());
        assert!(!DeclKind::Def.is_proposition());
    }

    #[test]
    fn summary_is_the_first_real_line_of_the_docstring() {
        let mut d = Decl::stub("Foo", "mathlib", "Mathlib.Foo");
        d.doc = Some("\n  The sum is monotone.\nMore detail.".into());
        assert_eq!(d.summary(), Some("The sum is monotone."));
    }

    /// Seventy-eight constants in Mathlib end in `.inner` and one of them is
    /// what nearly every row means: `Inner.inner` heads 376 of them, the next
    /// heads 8. Frequency is what tells an `export`ed name from a field on
    /// somebody's structure, among the rows that print the word bare.
    #[test]
    fn the_commonest_constant_with_a_name_comes_first() {
        let n = DeclName::new;
        let (inner, map, eq) = (n("Inner.inner"), n("Std.HashMap.inner"), n("Eq"));
        let rows = vec![
            ("inner x y = 0", vec![&inner, &eq]),
            ("inner x x = ‖x‖ ^ 2", vec![&inner, &inner, &eq]),
            ("m.inner = inner m", vec![&map, &eq]),
            ("inner m = m.inner", vec![&map, &inner]),
            ("inner (f x) = 1", vec![&map, &eq]),
        ];
        assert_eq!(
            commonest_called(rows.into_iter(), "inner"),
            vec![n("Inner.inner"), n("Std.HashMap.inner")]
        );
        // The last component, not a substring: `inner_apply` is not `inner`.
        let apply = n("Real.inner_apply");
        assert!(commonest_called([("inner_apply", vec![&apply])].into_iter(), "inner").is_empty());
    }

    #[test]
    fn a_word_is_printed_bare_when_no_namespace_and_no_binder_claims_it() {
        for ty in
            ["List.count false l = 0", "¬false = true", "(false, x)", "max a b ≤ c", "f\n  false"]
        {
            let word = if ty.contains("max") { "max" } else { "false" };
            assert!(prints_bare(ty, word), "{ty}");
        }
        for (ty, word) in [
            ("X.as = Y.as", "as"),
            ("∀ (as bs : List α), (as ++ bs).length = 0", "as"),
            ("∀ (val : α), u.copy val = val", "val"),
            ("∀ [inst : Monoid α], 1 = 1", "inst"),
            ("-{ val := x, neg := y } = 0", "neg"),
            ("falsehood = x", "false"),
            ("get? l = none", "get"),
            ("h' = h₁", "h"),
        ] {
            assert!(!prints_bare(ty, word), "{ty}");
        }
    }
}
