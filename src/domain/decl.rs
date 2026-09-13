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
    /// or the two head symbols agree.
    pub fn matches(&self, other: &ArgHead) -> bool {
        match self {
            ArgHead::Any => true,
            ArgHead::Named(a) => matches!(other, ArgHead::Named(b) if a == b),
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

    /// Whether `self`, read as a pattern, matches `other`, read as a statement.
    ///
    /// Argument matching is positional but tolerant of arity: a pattern with
    /// fewer arguments than the statement matches a prefix, because `Eq` and
    /// the order classes carry leading type and instance arguments a user never
    /// writes. A pattern with *more* arguments cannot match.
    pub fn matches(&self, other: &Shape) -> bool {
        if let Some(c) = &self.concl
            && other.concl.as_ref() != Some(c)
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

    /// Whether the row carries enough structure for shape search.
    pub fn shaped(&self) -> bool {
        self.elaborated && self.shape.concl.is_some()
    }

    /// First non-empty line of the docstring, for one-line result rows.
    pub fn summary(&self) -> Option<&str> {
        self.doc.as_deref().and_then(|d| d.lines().find(|l| !l.trim().is_empty())).map(str::trim)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape(concl: &str, args: &[&str]) -> Shape {
        Shape::new(Some(DeclName::new(concl)), args.iter().map(|a| ArgHead::parse(a)).collect())
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
}
