//! What `dt find` is asking for. A value object, plus the rule for whether a
//! declaration answers it.
//!
//! The rule lives here rather than in SQL so that it has one definition: the
//! SQLite adapter translates this into a query, the JSONL adapter evaluates it
//! directly, and the tests check the rule itself.

use crate::domain::decl::{ArgHead, Decl, DeclKind, Shape};
use crate::domain::name::DeclName;
use crate::domain::source::SourceId;

#[derive(Debug, Clone, Default)]
pub struct Query {
    /// Case-insensitive substring of the declaration name.
    pub name: Option<String>,
    /// Shape: conclusion head symbol and argument head symbols.
    pub shape: Shape,
    /// Constants the type must mention. Conditions combine with AND, because
    /// `--uses Real.exp,Finset.sum` means both.
    pub uses: Vec<DeclName>,
    /// Those of `uses` that were written inside the pattern rather than given
    /// as `--uses`. Not a condition of its own: it says how to *name* one, so
    /// that an empty result blames `` `List.range'` in the pattern `` rather
    /// than a flag the reader never typed.
    pub pattern_uses: Vec<DeclName>,
    /// For each argument of `shape`, the constants of `pattern_uses` written
    /// inside it and nowhere else: `Fin` in `MeasurableSpace (EuclideanSpace ℝ
    /// (Fin 3))`. An argument that matches only once unfolded has been
    /// rewritten, and what was inside it may be gone -- the instance that
    /// answers is about `WithLp p X` and mentions no `Fin` -- so they are asked
    /// of a statement only where the argument is the one written. Not a
    /// condition either; an argument past the end holds nothing.
    pub inside: Vec<Vec<DeclName>>,
    /// The arguments of `shape` that the pattern writes as a power of one
    /// term, by position, and how it writes each. Not a condition either: a
    /// shape keys on heads, and `x ^ 2` is `HPow.hPow` as `x ^ n` is, `x * x`
    /// `HMul.hMul` as `x * y` is. It ranks a row that writes them above one
    /// that only shares their heads, and says which arguments may be asked
    /// again spelled the other way. See [`Power`] and [`writes_powers`].
    pub powers: Vec<(usize, Power)>,
    /// Module prefix, e.g. `Mathlib.Analysis`.
    pub module: Option<String>,
    pub source: Option<SourceId>,
    /// Any of these kinds; empty is every kind.
    pub kind: Vec<DeclKind>,
    /// Free-text words over type and docstring. ANDed, like `uses`: the flag
    /// repeats, and a `--text` given several words is those words, because
    /// that is what the text index does with them anyway.
    pub text: Vec<String>,
    /// Restrict to rows that came out of the elaborator.
    pub elaborated_only: bool,
    /// Drop rows whose proof is `sorry`.
    pub no_sorry: bool,
    /// Include what the compiler generated. See [`Decl::is_generated`].
    pub generated: bool,
    pub limit: usize,
}

/// A term multiplied by itself a numeral number of times, and how that is
/// written. Mathlib spells a power both ways, often for the same fact --
/// `sq_nonneg` is about `a ^ 2` and `mul_self_nonneg` about `a * a`,
/// `pow_three'` says `a ^ 3 = a * a * a` -- and the index, which keeps heads
/// only, has the two as `HPow.hPow` and `HMul.hMul`: as far as a shape can
/// tell they are different questions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Power {
    /// How many factors of the term there are: 2 for a square, 3 for a cube.
    pub exponent: u32,
    pub spelling: Spelling,
}

/// How a [`Power`] is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Spelling {
    /// With `^`: `x ^ 3`.
    Pow,
    /// As the product of its factors, grouped any way: `x * x * x`, `x * (x *
    /// x)`, `x ^ 2 * x`.
    Mul,
}

impl Power {
    /// The head symbol a power written this way has.
    pub fn head(self) -> DeclName {
        DeclName::new(match self.spelling {
            Spelling::Pow => "HPow.hPow",
            Spelling::Mul => "HMul.hMul",
        })
    }

    /// The same power, written the other way.
    pub fn respelled(self) -> Power {
        let spelling = match self.spelling {
            Spelling::Pow => Spelling::Mul,
            Spelling::Mul => Spelling::Pow,
        };
        Power { spelling, ..self }
    }

    /// Whether a statement has the signs a power this size needs, read off its
    /// bytes. Only `*` is ever read as a product and only `^` as a power, so a
    /// statement without them writes none, whatever else it says.
    ///
    /// A quick no, and nothing more: it says a statement could write the
    /// power, never that it does. That is what makes it worth asking. Reading
    /// a statement for its powers costs ten microseconds and this costs a
    /// scan, and 71% of the 6564 `Eq` rows of Mathlib with a product are short
    /// of the three signs `x * x * x * x` needs.
    pub fn signs_in(self, statement: &str) -> bool {
        match self.spelling {
            // Written `^`, the power is one at its top.
            Spelling::Pow => statement.contains('^'),
            // Written `*`, it is a product at its top, and its `n` factors are
            // `n - 1` products -- unless a `^` writes several of them at once,
            // as `x ^ 3 * x` does.
            Spelling::Mul => {
                let signs = statement.bytes().filter(|b| *b == b'*').count() as u32;
                signs > 0 && (signs + 1 >= self.exponent || statement.contains('^'))
            }
        }
    }
}

/// Ten, not forty. A search is read in full by whoever asked it, and the
/// eleventh hit for a query worth answering is almost never the one that was
/// wanted — a query that needs forty rows needs refining, and `dt find` says so
/// when the limit hid something.
pub const DEFAULT_LIMIT: usize = 10;

impl Query {
    pub fn new() -> Query {
        Query { limit: DEFAULT_LIMIT, ..Default::default() }
    }

    /// Whether the query constrains anything at all. An unconstrained query
    /// would return the first `limit` rows of the corpus, which is never what
    /// was meant.
    pub fn is_empty(&self) -> bool {
        self.name.is_none()
            && self.shape.is_empty()
            && self.uses.is_empty()
            && self.module.is_none()
            && self.source.is_none()
            && self.kind.is_empty()
            && self.text.is_empty()
    }

    /// The query's conditions, each on its own, for explaining an empty result.
    ///
    /// "No match" has two causes that need opposite repairs. Either one
    /// condition matches nothing in the corpus at all — a misspelled constant,
    /// a module prefix that is not a prefix, a source that does not exist — and
    /// the fix is to edit that flag; or every condition matches something and
    /// no row satisfies all of them, and the fix is to drop one. A caller told
    /// only "no match" cannot tell which, and guessing costs a round trip
    /// either way, which is the expensive kind of waste.
    ///
    /// Each probe asks for one row, so the whole diagnosis costs about as much
    /// as the search that failed.
    pub fn conditions(&self) -> Vec<(String, Query)> {
        let one = |q: Query| Query { limit: 1, ..q };
        let mut out = Vec::new();
        if let Some(n) = &self.name {
            out.push((format!("--name {n}"), one(Query { name: Some(n.clone()), ..Query::new() })));
        }
        if let Some(c) = &self.shape.concl {
            let shape = Shape { concl: Some(c.clone()), args: Vec::new() };
            out.push((format!("--concl {c}"), one(Query { shape, ..Query::new() })));
        }
        // An argument head is written inside the pattern, not as a flag, so it
        // is named the way the user wrote it rather than the way it is stored.
        for a in &self.shape.args {
            if let Some(n) = a.name() {
                let shape = Shape { concl: None, args: vec![a.clone()] };
                out.push((format!("`{n}` in the pattern"), one(Query { shape, ..Query::new() })));
            }
        }
        for c in &self.uses {
            let label = if self.pattern_uses.contains(c) {
                format!("`{c}` in the pattern")
            } else {
                format!("--uses {c}")
            };
            out.push((label, one(Query { uses: vec![c.clone()], ..Query::new() })));
        }
        if let Some(m) = &self.module {
            out.push((format!("--in {m}"), one(Query { module: Some(m.clone()), ..Query::new() })));
        }
        if let Some(s) = &self.source {
            out.push((
                format!("--source {s}"),
                one(Query { source: Some(s.clone()), ..Query::new() }),
            ));
        }
        // One condition however many kinds it names: the list is an `or`, and
        // blaming one kind of it would be blaming something that cannot fail
        // alone.
        if !self.kind.is_empty() {
            let named: Vec<&str> = self.kind.iter().map(DeclKind::as_str).collect();
            out.push((
                format!("--kind {}", named.join(",")),
                one(Query { kind: self.kind.clone(), ..Query::new() }),
            ));
        }
        for x in &self.text {
            out.push((format!("--text {x}"), one(Query { text: vec![x.clone()], ..Query::new() })));
        }
        out
    }

    /// Whether answering the query requires elaborated rows. Asking for a shape
    /// implies it: a text row has no conclusion head symbol, so including it
    /// would silently drop the condition.
    pub fn needs_shape(&self) -> bool {
        !self.shape.is_empty()
    }

    pub fn matches(&self, d: &Decl) -> bool {
        if self.elaborated_only && !d.elaborated {
            return false;
        }
        if self.needs_shape() && !d.shaped() {
            return false;
        }
        if self.no_sorry && d.has_sorry {
            return false;
        }
        if !self.generated && d.is_generated() {
            return false;
        }
        if let Some(n) = &self.name
            && !d.name.as_str().to_lowercase().contains(&n.to_lowercase())
        {
            return false;
        }
        if !self.answers_shape_and_uses(d) {
            return false;
        }
        if let Some(m) = &self.module
            && !d.module.is_under(m)
        {
            return false;
        }
        if let Some(s) = &self.source
            && &d.source != s
        {
            return false;
        }
        if !self.kind.is_empty() && !self.kind.contains(&d.kind) {
            return false;
        }
        // Each word on its own, and either field: the text index treats the
        // three columns of a row as one document, so a word in the type and a
        // word in the docstring is a match there and has to be one here.
        for t in &self.text {
            let t = t.to_lowercase();
            let in_type = d.ty.to_lowercase().contains(&t);
            let in_doc = d.doc.as_deref().is_some_and(|s| s.to_lowercase().contains(&t));
            if !in_type && !in_doc {
                return false;
            }
        }
        true
    }

    /// Whether `d` has the shape and mentions every use, as one condition: a
    /// use written inside an argument is excused where that argument matched
    /// only once unfolded. See [`Query::inside`].
    pub fn answers_shape_and_uses(&self, d: &Decl) -> bool {
        if !self.unfolds() {
            return self.shape.matches(&d.shape) && self.uses.iter().all(|c| mentions(d, c));
        }
        self.shape
            .alignments(&d.shape)
            .any(|s| self.uses.iter().all(|c| mentions(d, c) || self.excused(c, &s)))
    }

    /// Whether an argument of the shape can match through an unfolding.
    pub fn unfolds(&self) -> bool {
        self.shape.args.iter().any(|a| matches!(a, ArgHead::Reducible { .. }))
    }

    /// The uses a statement may leave out and still answer: those written
    /// only inside arguments that can match through an unfolding. Which of
    /// the statements that leave one out answer is a question of alignment,
    /// asked row by row.
    pub fn excusable(&self) -> Vec<&DeclName> {
        self.uses.iter().filter(|c| !self.instead_of(c).is_empty()).collect()
    }

    /// What a statement that leaves out `c` has among its heads instead, if
    /// it may leave it out at all: for each argument `c` was written inside,
    /// the names other than the one written that it matches once unfolded.
    /// One of each, or the statement matched an argument as written and has
    /// to mention `c`. Empty for a use every statement has to mention.
    pub fn instead_of(&self, c: &DeclName) -> Vec<Vec<&DeclName>> {
        let mut out = Vec::new();
        for i in self.holders(c) {
            let Some(ArgHead::Reducible { written, class }) = self.shape.args.get(i) else {
                return Vec::new();
            };
            out.push(class.iter().filter(|m| *m != written).collect());
        }
        out
    }

    /// Whether an alignment excuses `c`: every argument it was written inside
    /// matched only once unfolded.
    fn excused(&self, c: &DeclName, alignment: &[Option<&DeclName>]) -> bool {
        let holders = self.holders(c);
        !holders.is_empty()
            && holders.into_iter().all(|i| alignment.get(i).is_some_and(Option::is_some))
    }

    /// The arguments `c` was written inside.
    fn holders(&self, c: &DeclName) -> Vec<usize> {
        (0..self.inside.len()).filter(|i| self.inside[*i].contains(c)).collect()
    }

    /// What `d` matched only once unfolded, as the head written and the
    /// statement's: empty where it answers as written.
    pub fn unfolded(&self, d: &Decl) -> Vec<(DeclName, DeclName)> {
        if !self.unfolds() {
            return Vec::new();
        }
        let answers: Vec<Vec<Option<&DeclName>>> = self
            .shape
            .alignments(&d.shape)
            .filter(|s| self.uses.iter().all(|c| mentions(d, c) || self.excused(c, s)))
            .collect();
        if answers.iter().any(|s| s.iter().all(Option::is_none)) {
            return Vec::new();
        }
        let Some(first) = answers.first() else { return Vec::new() };
        self.shape
            .args
            .iter()
            .zip(first)
            .filter_map(|(p, m)| Some((p.name()?.clone(), (*m)?.clone())))
            .collect()
    }
}

/// Equality on the conditions only: `limit` and the two boolean switches are
/// presentation, not part of what is being asked. Used by the pattern tests.
impl PartialEq for Query {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.shape == other.shape
            && self.uses == other.uses
            && self.module == other.module
            && self.source == other.source
            && self.kind == other.kind
            && self.text == other.text
    }
}

impl Eq for Query {}

/// How well a result answers the query, for ordering. How much of the name the
/// query accounted for, then shape agreement, then how much of the type is
/// spent on things the query did not ask for: a two-line lemma about exactly
/// the right constants beats a long one that happens to mention them.
pub fn rank(q: &Query, d: &Decl) -> (u32, usize) {
    let mut score = 0;
    if let Some(n) = &q.name {
        score += name_score(n, d);
    }
    if let (Some(asked), Some(concl)) = (&q.shape.concl, &d.shape.concl)
        && crate::domain::decl::keyed_as(asked).iter().any(|k| k.names(concl))
    {
        score += 4;
    }
    // Shape agreement too, one step finer than the heads the index keeps:
    // every product agrees with `a * a` there.
    if !q.powers.is_empty() && writes_powers(q, d) {
        score += 4;
    }
    // And one step coarser: a statement about the head written outranks one
    // about another name for it, which is found only once both are unfolded.
    if q.unfolds() && q.unfolded(d).is_empty() {
        score += 4;
    }
    score += q.uses.iter().filter(|c| mentions(d, c)).count() as u32;
    if d.has_sorry {
        score = score.saturating_sub(2);
    }
    // Descending score, then ascending type length.
    (u32::MAX - score, d.ty.len())
}

/// Whether the statement writes each power the query does, spelled the way
/// the query spells it, on the side the query has it. The index keys on heads
/// and has `HMul.hMul` for `x * x` and for `x * y` alike, and only the
/// statement tells them apart. A query that writes no power asks for none.
pub fn writes_powers(q: &Query, d: &Decl) -> bool {
    q.powers.is_empty()
        // Asked of every row a search finds, and of the same row once a look,
        // so the statements that cannot answer are turned away before they are
        // read. See [`Power::signs_in`].
        || (q.powers.iter().all(|(_, p)| p.signs_in(&d.ty)) && {
            let has = crate::domain::pattern::powers_in(&d.ty);
            q.powers.iter().all(|p| has.contains(p))
        })
}

/// Whether the type mentions a constant the query names. See
/// [`DeclName::names`].
fn mentions(d: &Decl, asked: &DeclName) -> bool {
    d.consts.iter().any(|c| asked.names(c))
}

/// How much of the row's name `--name` accounts for.
///
/// The filter is a substring test, which is the right filter and no ordering
/// at all: `Real.sin_sq` came fourth behind three of its own suffixes, sorted
/// by type length like everything else. A name given in full is a request for
/// that declaration, and one given without its namespace is a request for the
/// declaration called that -- both outrank a row that merely begins with it,
/// which in turn outranks one that contains it somewhere in the middle.
///
/// It outscores the shape agreement below deliberately. A caller who writes
/// the whole name has said which row they want, and nothing else in the query
/// says it more precisely.
fn name_score(asked: &str, d: &Decl) -> u32 {
    let asked = asked.to_lowercase();
    let name = d.name.as_str().to_lowercase();
    if name == asked {
        8
    } else if d.name.base().to_lowercase() == asked {
        6
    } else if name.starts_with(&asked) {
        2
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::decl::ArgHead;

    fn decl() -> Decl {
        let mut d =
            Decl::stub("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Complex.Exponential");
        d.ty = "∀ {x y : ℝ}, Real.exp x ≤ Real.exp y ↔ x ≤ y".into();
        d.shape = Shape::new(
            Some(DeclName::new("Iff")),
            vec![ArgHead::parse("LE.le"), ArgHead::parse("LE.le")],
        );
        d.consts = ["Iff", "LE.le", "Real.exp"].iter().map(|s| DeclName::new(*s)).collect();
        d.doc = Some("`exp` is monotone.".into());
        d
    }

    /// The report: `--name Real.sin_sq` put `Real.sin_sq` fourth, behind three
    /// of its own suffixes, because within the substring matches nothing
    /// preferred the row whose name *is* the query. Past the default limit
    /// that reads as "not indexed" rather than "look further down".
    #[test]
    fn a_list_of_kinds_is_any_of_them_and_one_condition() {
        let mut q = Query::new();
        q.kind = vec![DeclKind::Def, DeclKind::Structure];
        let mut d = decl();
        assert!(!q.matches(&d), "a theorem is neither");
        d.kind = DeclKind::Structure;
        assert!(q.matches(&d));
        let labels: Vec<String> = q.conditions().into_iter().map(|(l, _)| l).collect();
        assert_eq!(labels, vec!["--kind def,structure"]);
    }

    #[test]
    fn a_kind_is_named_or_refused() {
        assert_eq!(DeclKind::named("abbrev"), Some(DeclKind::Def));
        assert_eq!(DeclKind::named("opaque"), Some(DeclKind::Other("opaque".into())));
        assert_eq!(DeclKind::named("def,structure"), None);
    }

    #[test]
    fn a_constant_written_in_the_pattern_is_not_called_a_flag() {
        let mut q = Query::new();
        q.uses = vec![DeclName::new("List.take"), DeclName::new("Real.exp")];
        q.pattern_uses = vec![DeclName::new("List.take")];
        let labels: Vec<String> = q.conditions().into_iter().map(|(l, _)| l).collect();
        assert_eq!(labels, vec!["`List.take` in the pattern", "--uses Real.exp"]);
    }

    #[test]
    fn a_name_given_in_full_ranks_above_the_names_that_extend_it() {
        let named = |n: &str| {
            let mut d = Decl::stub(n, "mathlib", "Mathlib.Analysis.Trigonometric");
            // Shorter type, so the old tie-break would have put it first.
            d.ty = "short".into();
            d
        };
        let mut q = Query::new();
        q.name = Some("Real.sin_sq".into());
        let exact = Decl::stub("Real.sin_sq", "mathlib", "Mathlib.Analysis.Trigonometric");
        assert!(rank(&q, &exact) < rank(&q, &named("Real.sin_sq_le_one")));
        // A prefix of the query still beats a row that merely contains it.
        assert!(
            rank(&q, &named("Real.sin_sq_le_one")) < rank(&q, &named("Complex.of_Real.sin_sq"))
        );
        // Unqualified: the row called that is the row that was asked for,
        // whichever namespace it is in.
        q.name = Some("sin_sq".into());
        assert!(rank(&q, &exact) < rank(&q, &named("Real.sin_sq_le_one")));
        // And the filter is case-insensitive, so the ranking is too.
        q.name = Some("REAL.SIN_SQ".into());
        assert!(rank(&q, &exact) < rank(&q, &named("Real.sin_sq_le_one")));
    }

    #[test]
    fn an_empty_query_is_recognised_as_empty() {
        assert!(Query::new().is_empty());
        let mut q = Query::new();
        q.name = Some("exp".into());
        assert!(!q.is_empty());
    }

    #[test]
    fn uses_combine_with_and() {
        let d = decl();
        let mut q = Query::new();
        q.uses = vec![DeclName::new("Real.exp"), DeclName::new("LE.le")];
        assert!(q.matches(&d));
        q.uses.push(DeclName::new("Finset.sum"));
        assert!(!q.matches(&d));
    }

    /// `--uses .length`, which `l.length` in a pattern comes to, is whichever
    /// `length` the type mentions, and ranks as the constant itself would.
    #[test]
    fn a_field_is_mentioned_in_any_namespace() {
        let mut d = decl();
        d.consts.push(DeclName::new("List.length"));
        let mut q = Query::new();
        q.uses = vec![DeclName::new(".length")];
        assert!(q.matches(&d));
        let mut exact = q.clone();
        exact.uses = vec![DeclName::new("List.length")];
        assert_eq!(rank(&q, &d), rank(&exact, &d));
        q.uses = vec![DeclName::new(".lengthTR")];
        assert!(!q.matches(&d));
        // And a conclusion named by its field outranks one that is not it.
        d.shape.concl = Some(DeclName::new("List.Nodup"));
        let mut other = d.clone();
        other.shape.concl = Some(DeclName::new("List.Sorted"));
        q.uses = Vec::new();
        q.shape = Shape::new(Some(DeclName::new(".Nodup")), Vec::new());
        assert!(rank(&q, &d) < rank(&q, &other));
    }

    #[test]
    fn name_match_is_case_insensitive_substring() {
        let d = decl();
        let mut q = Query::new();
        q.name = Some("EXP_LE".into());
        assert!(q.matches(&d));
        q.name = Some("sum".into());
        assert!(!q.matches(&d));
    }

    #[test]
    fn a_shape_query_never_returns_text_rows() {
        let mut d = decl();
        d.elaborated = false;
        d.shape = Shape::default();
        let mut q = Query::new();
        q.shape = Shape::new(Some(DeclName::new("Iff")), vec![]);
        assert!(!q.matches(&d), "a text row has no shape and must not match silently");
    }

    #[test]
    fn module_filter_respects_component_boundaries() {
        let d = decl();
        let mut q = Query::new();
        q.module = Some("Mathlib.Analysis".into());
        assert!(q.matches(&d));
        q.module = Some("Mathlib.Order".into());
        assert!(!q.matches(&d));
    }

    #[test]
    fn text_search_covers_type_and_docstring() {
        let d = decl();
        let mut q = Query::new();
        q.text = vec!["monotone".into()];
        assert!(q.matches(&d));
        q.text = vec!["↔".into()];
        assert!(q.matches(&d));
        q.text = vec!["Finset".into()];
        assert!(!q.matches(&d));
    }

    /// The report: `--text summable --text monotone` was refused by the
    /// parser rather than answered. Two words are two conditions, which is
    /// what the text index makes of them anyway.
    #[test]
    fn text_words_combine_with_and() {
        let d = decl();
        let mut q = Query::new();
        // One word out of the type and one out of the docstring: a row is one
        // document to the text index, so it is one row here too.
        q.text = vec!["Real.exp".into(), "monotone".into()];
        assert!(q.matches(&d));
        q.text.push("Finset".into());
        assert!(!q.matches(&d));
        // And each word is a condition of its own, so an empty result can
        // name the one that matched nothing.
        let labels: Vec<String> = q.conditions().into_iter().map(|(l, _)| l).collect();
        assert!(labels.contains(&"--text Finset".to_string()), "{labels:?}");
    }

    #[test]
    fn sorry_rows_rank_below_proved_ones() {
        let good = decl();
        let mut bad = decl();
        bad.has_sorry = true;
        let mut q = Query::new();
        q.uses = vec![DeclName::new("Real.exp")];
        assert!(rank(&q, &good) < rank(&q, &bad));
    }

    /// `0 ≤ a * a` put `mul_self_nonneg` behind every shorter product: the
    /// heads are the same, and the square is only in the statement.
    #[test]
    fn a_row_that_writes_the_power_ranks_above_a_shorter_one_that_does_not() {
        let stating = |ty: &str| Decl { ty: ty.into(), ..decl() };
        let square = stating("∀ {R : Type u} [inst : Semiring R] (a : R), 0 ≤ a * a");
        let product = stating("∀ (r : ℝ), 0 ≤ r.sign * r");
        let mut q = Query::new();
        q.shape = Shape::new(
            Some(DeclName::new("LE.le")),
            vec![ArgHead::parse("OfNat.ofNat"), ArgHead::parse("HMul.hMul")],
        );
        // By length, as ever, where the pattern writes no power.
        assert!(rank(&q, &product) < rank(&q, &square));
        q.powers = vec![(1, Power { exponent: 2, spelling: Spelling::Mul })];
        assert!(rank(&q, &square) < rank(&q, &product));
    }

    /// `EuclideanSpace` is `PiLp`, which is `WithLp`, once unfolded.
    fn unfolding(written: &str) -> ArgHead {
        let class = ["EuclideanSpace", "PiLp", "WithLp"].map(DeclName::new).to_vec();
        ArgHead::Reducible { written: DeclName::new(written), class }
    }

    /// `MeasurableSpace (EuclideanSpace ℝ (Fin 3))`, as a search asks it.
    fn measurable_euclidean() -> Query {
        let mut q = Query::new();
        q.shape =
            Shape::new(Some(DeclName::new("MeasurableSpace")), vec![unfolding("EuclideanSpace")]);
        q.uses = vec![DeclName::new("Fin")];
        q.pattern_uses = q.uses.clone();
        q.inside = vec![vec![DeclName::new("Fin")]];
        q
    }

    /// An instance of `MeasurableSpace` for `head`, mentioning `consts` too.
    fn instance(name: &str, head: &str, consts: &[&str]) -> Decl {
        let mut d = Decl::stub(name, "mathlib", "Mathlib.Analysis.Normed.Lp.MeasurableSpace");
        d.kind = DeclKind::Instance;
        d.ty = format!("MeasurableSpace ({head} p X)");
        d.shape = Shape::new(Some(DeclName::new("MeasurableSpace")), vec![ArgHead::parse(head)]);
        d.consts =
            ["MeasurableSpace", head].iter().chain(consts).map(|c| DeclName::new(*c)).collect();
        d
    }

    /// The report: the instance Lean finds for `EuclideanSpace ℝ (Fin 3)` is
    /// stated for `WithLp p X`, and says nothing of `Fin`. Where the argument
    /// is the one written, what was written inside it is still asked.
    #[test]
    fn a_use_written_inside_an_unfolded_argument_is_excused_there_and_only_there() {
        let q = measurable_euclidean();
        assert_eq!(q.excusable(), [&DeclName::new("Fin")]);
        let with_lp = instance("WithLp.measurableSpace", "WithLp", &[]);
        assert!(q.matches(&with_lp));
        assert_eq!(
            q.unfolded(&with_lp),
            [(DeclName::new("EuclideanSpace"), DeclName::new("WithLp"))]
        );
        assert!(!q.matches(&instance("EuclideanSpace.inst", "EuclideanSpace", &[])));
        let fin = instance("EuclideanSpace.inst", "EuclideanSpace", &["Fin"]);
        assert!(q.matches(&fin));
        assert!(q.unfolded(&fin).is_empty());
    }

    /// A use written outside the argument as well, or given as a flag, is
    /// asked of every statement, however the argument matched.
    #[test]
    fn a_use_written_outside_an_unfolded_argument_is_asked_of_every_statement() {
        let mut q = measurable_euclidean();
        q.inside = vec![Vec::new()];
        assert!(q.excusable().is_empty());
        assert!(!q.matches(&instance("WithLp.measurableSpace", "WithLp", &[])));
        assert!(q.matches(&instance("WithLp.measurableSpace", "WithLp", &["Fin"])));
    }

    #[test]
    fn a_use_inside_two_arguments_is_excused_only_where_both_were_unfolded() {
        let eq = |l: &str, r: &str| {
            let mut d = decl();
            d.shape =
                Shape::new(Some(DeclName::new("Eq")), vec![ArgHead::parse(l), ArgHead::parse(r)]);
            d.consts = ["Eq", l, r].map(DeclName::new).to_vec();
            d
        };
        let mut q = Query::new();
        q.shape = Shape::new(
            Some(DeclName::new("Eq")),
            vec![unfolding("EuclideanSpace"), unfolding("PiLp")],
        );
        q.uses = vec![DeclName::new("Fin")];
        q.inside = vec![vec![DeclName::new("Fin")], vec![DeclName::new("Fin")]];
        assert!(q.matches(&eq("WithLp", "WithLp")));
        assert!(!q.matches(&eq("EuclideanSpace", "WithLp")), "one side is as written");
        q.shape.args[1] = ArgHead::parse("PiLp");
        assert!(q.excusable().is_empty(), "one side cannot be unfolded");
        assert!(!q.matches(&eq("WithLp", "PiLp")));
    }

    /// What a statement that leaves out `Fin` has among its heads instead,
    /// which the SQL asks of a row before any alignment is: a name the
    /// argument unfolds to other than the one written, since a statement
    /// about that one has to mention `Fin` -- one for each argument it is in.
    #[test]
    fn a_use_is_left_out_for_another_name_of_each_argument_it_is_inside() {
        let instead = |q: &Query| -> Vec<Vec<String>> {
            let names = q.instead_of(&DeclName::new("Fin"));
            names.iter().map(|v| v.iter().map(|n| n.to_string()).collect()).collect()
        };
        let mut q = measurable_euclidean();
        assert_eq!(instead(&q), [["PiLp", "WithLp"]]);
        q.shape.args.push(unfolding("PiLp"));
        q.inside.push(vec![DeclName::new("Fin")]);
        assert_eq!(instead(&q), [["PiLp", "WithLp"], ["EuclideanSpace", "WithLp"]]);
        q.shape.args[1] = ArgHead::parse("PiLp");
        assert!(instead(&q).is_empty(), "one argument can only match as written");
    }

    /// Both are the same instance to Lean. The one about the name the reader
    /// wrote is the one they were looking for, even when it is the longer.
    #[test]
    fn a_statement_about_the_head_written_ranks_above_one_about_another_name() {
        let q = measurable_euclidean();
        let mut written = instance("EuclideanSpace.inst", "EuclideanSpace", &["Fin"]);
        written.ty = format!("{} and a good deal more", written.ty);
        let other = instance("PiLp.inst", "PiLp", &["Fin"]);
        assert!(rank(&q, &written) < rank(&q, &other));
    }

    /// The quick no must never be the wrong answer, and that is checked
    /// against the whole of Mathlib elsewhere. Here is what it turns away and
    /// what it has to let through.
    #[test]
    fn a_statement_short_of_multiplication_signs_writes_no_power() {
        let mul = |exponent| Power { exponent, spelling: Spelling::Mul };
        let pow = |exponent| Power { exponent, spelling: Spelling::Pow };
        assert!(!mul(2).signs_in("0 ≤ a + a"), "a sum is no product");
        assert!(mul(2).signs_in("0 ≤ a * a"));
        assert!(!mul(4).signs_in("a * b = b * a"), "three signs short of four factors");
        assert!(mul(4).signs_in("a * a * a * a = b"));
        // A `^` writes several factors at once, so the count says nothing --
        // but a power written `*` is still a product at its top.
        assert!(mul(4).signs_in("a ^ 3 * a = b"));
        assert!(!mul(4).signs_in("a ^ 4 = b"));
        assert!(!pow(2).signs_in("a * a = b"), "a product is not written `^`");
        assert!(pow(2).signs_in("a ^ 2 = b"));
    }
}
