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
            if let ArgHead::Named(n) = a {
                let shape = Shape { concl: None, args: vec![ArgHead::Named(n.clone())] };
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
        if !self.shape.matches(&d.shape) {
            return false;
        }
        if !self.uses.iter().all(|c| d.consts.contains(c)) {
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
    if q.shape.concl.is_some() && q.shape.concl == d.shape.concl {
        score += 4;
    }
    score += q.uses.iter().filter(|c| d.consts.contains(c)).count() as u32;
    if d.has_sorry {
        score = score.saturating_sub(2);
    }
    // Descending score, then ascending type length.
    (u32::MAX - score, d.ty.len())
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
}
