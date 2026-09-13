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
    /// Module prefix, e.g. `Mathlib.Analysis`.
    pub module: Option<String>,
    pub source: Option<SourceId>,
    pub kind: Option<DeclKind>,
    /// Free text over type and docstring.
    pub text: Option<String>,
    /// Restrict to rows that came out of the elaborator.
    pub elaborated_only: bool,
    /// Drop rows whose proof is `sorry`.
    pub no_sorry: bool,
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
            && self.kind.is_none()
            && self.text.is_none()
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
            out.push((format!("--uses {c}"), one(Query { uses: vec![c.clone()], ..Query::new() })));
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
        if let Some(k) = &self.kind {
            out.push((format!("--kind {k}"), one(Query { kind: Some(k.clone()), ..Query::new() })));
        }
        if let Some(x) = &self.text {
            out.push((format!("--text {x}"), one(Query { text: Some(x.clone()), ..Query::new() })));
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
        if let Some(k) = &self.kind
            && &d.kind != k
        {
            return false;
        }
        if let Some(t) = &self.text {
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

/// How well a result answers the query, for ordering. Shape agreement first,
/// then how much of the type is spent on things the query did not ask for: a
/// two-line lemma about exactly the right constants beats a long one that
/// happens to mention them.
pub fn rank(q: &Query, d: &Decl) -> (u32, usize) {
    let mut score = 0;
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
        q.text = Some("monotone".into());
        assert!(q.matches(&d));
        q.text = Some("↔".into());
        assert!(q.matches(&d));
        q.text = Some("Finset".into());
        assert!(!q.matches(&d));
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
