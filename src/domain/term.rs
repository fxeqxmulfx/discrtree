//! Positioned types and numeric literals, matched against expressions read by Lean.

use crate::domain::name::DeclName;
use crate::domain::numeral::Scientific;
use crate::domain::pattern::COERCION;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// The head of `↑e x` in a pattern: `e` coerced to a function, by whatever
/// coercion its type has, and applied to `x`. No row has it. A row has the
/// coercion's own head, `DFunLike.coe` for an `Equiv` and
/// `PartialHomeomorph.toFun'` for a `PartialHomeomorph`, and which one is for
/// the type of `e` to say.
pub const COERCED: &str = "$coe";

/// What matching a pattern's term to a row's has found: the term each of the
/// row's variables is specialized to, consistently, and how many of the
/// pattern's wildcards met more than a variable. See [`Term::specifics`].
#[derive(Debug, Clone, Default)]
struct Matching {
    assigned: BTreeMap<usize, Term>,
    specific: usize,
}

/// An application, a telescope variable, a literal, or a wildcard. `ty` is
/// recorded for terms, but not recursively for the terms making up their types.
/// A query's `ty` is an ascription, and its `implicit` is the spelling `@`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Term {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub variable: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub literal: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub args: Vec<Term>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub explicit: Option<Vec<usize>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ty: Option<Box<Term>>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub implicit: bool,
    /// A query argument eligible for the existing power/product retry.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub power: Option<u32>,
}

impl Term {
    pub fn named(head: impl Into<String>, args: Vec<Term>) -> Self {
        Self { head: Some(head.into()), args, ..Self::default() }
    }

    pub fn matches(&self, other: &Term) -> bool {
        self.match_with(other, &mut Matching::default())
    }

    /// Where the row's term matches, how many of the pattern's wildcards it
    /// has something particular for: a constant, or a term made of more than
    /// a variable. None where the row states what the pattern writes, or
    /// more, and one for each place it states it of a particular term:
    /// `e.symm (e x) = x` is `Equiv.symm_apply_apply` as written, and
    /// `Cardinal.preAleph.symm ↑n = ↑n` with three such places.
    pub fn specifics(&self, other: &Term) -> Option<usize> {
        let mut m = Matching::default();
        self.match_with(other, &mut m).then_some(m.specific)
    }

    fn match_with(&self, other: &Term, m: &mut Matching) -> bool {
        if let Some(ty) = &self.ty
            && !other.ty.as_ref().is_some_and(|actual| ty.match_with(actual, m))
        {
            return false;
        }
        if self.head.is_none() && self.literal.is_none() && self.args.is_empty() {
            if other.variable.is_none() || !other.args.is_empty() {
                m.specific += 1;
            }
            return true;
        }
        // A map applied is one application, wherever its coercions are: a
        // pattern has no types to put them where Lean does. Tried before the
        // terms as they are, and as well as them, because a parameter the row
        // applies through one is a map the pattern's may specialize. Not for
        // `↑e x` against a row that applies no `DFunLike.coe`: there `e` is
        // what the row's own coercion is applied to, and the terms as they
        // are line up.
        if other.coerces() || (self.coerces() && self.head.as_deref() != Some(COERCED)) {
            let before = m.clone();
            if self.match_applied(other, m) {
                return true;
            }
            *m = before;
        }
        // Telescope parameters may be specialized, consistently across every
        // occurrence. `α` cannot be both Nat and Int in one answer.
        if let Some(var) = other.variable {
            let mut value = self.clone();
            value.ty = None;
            if !other.args.is_empty() {
                value.args.clear();
            }
            if value.head.as_deref() == Some(COERCED) {
                value.head = None;
            }
            let consistent = match m.assigned.get_mut(&var) {
                Some(previous) => previous.merge(&value),
                None => {
                    m.assigned.insert(var, value);
                    true
                }
            };
            if other.args.is_empty() {
                return consistent;
            }
            let args = other.visible_args();
            return consistent
                && self.args.len() == args.len()
                && self.args.iter().zip(args).all(|(asked, actual)| asked.match_with(actual, m));
        }
        if let Some(exponent) = self.power
            && self.head != other.head
            && matches!(other.head.as_deref(), Some("HPow.hPow" | "HMul.hMul"))
        {
            return self.match_power(other, exponent, m);
        }
        // A variable applied, where the row applies a constant.
        if self.head.is_none() && self.literal.is_none() && other.head.is_some() {
            m.specific += 1;
        }
        if let Some(head) = self.head.as_ref().filter(|h| *h != COERCED)
            && !other.head.as_ref().is_some_and(|actual| {
                let asked = DeclName::new(head);
                asked.names(&DeclName::new(actual))
                    || (!matches!(head.as_str(), "Real" | "Complex" | "Nat" | "Int" | "Rat")
                        && asked.abbreviates(&DeclName::new(actual)))
            })
        {
            return false;
        }
        if let Some(literal) = &self.literal
            && other.literal.as_ref() != Some(literal)
        {
            return false;
        }
        if let Some(ours) = self.scientific()
            && self.args.iter().all(|arg| arg.ty.is_none())
            && let Some(theirs) = other.scientific()
        {
            return ours == theirs;
        }
        let args = if self.implicit { other.args.iter().collect() } else { other.visible_args() };
        args.len() >= self.args.len()
            && self.args.iter().zip(args).all(|(asked, actual)| asked.match_with(actual, m))
    }

    fn visible_args(&self) -> Vec<&Term> {
        match &self.explicit {
            Some(indices) => indices.iter().filter_map(|i| self.args.get(*i)).collect(),
            None => self.args.iter().collect(),
        }
    }

    /// Whether this applies a map through [`COERCION`], as Lean elaborates a
    /// bundled map applied, and is not written with `@`; or, in a pattern,
    /// through whichever coercion [`COERCED`] stands for.
    fn coerces(&self) -> bool {
        !self.implicit
            && matches!(self.head.as_deref(), Some(COERCION | COERCED))
            && !self.visible_args().is_empty()
    }

    /// What is applied, and every term it is applied to, through each
    /// coercion: `⇑(⇑(fderiv 𝕜 f x) v) w` is `fderiv` applied to `𝕜 f x v w`.
    /// Lean puts in a coercion for each map a map returns, and prints none.
    fn spine(&self) -> (&Term, Vec<&Term>) {
        let args = self.visible_args();
        if !self.coerces() {
            return (self, args);
        }
        let (applied, mut all) = args[0].spine();
        all.extend(&args[1..]);
        (applied, all)
    }

    /// [`Term::match_with`] of the two applications through their
    /// coercions: what each applies, by its head alone, and then the terms,
    /// the pattern's a prefix of the row's.
    fn match_applied(&self, other: &Term, m: &mut Matching) -> bool {
        let (ours, asked) = self.spine();
        let (theirs, actual) = other.spine();
        let bare = |t: &Term| Term {
            head: t.head.clone(),
            variable: t.variable,
            literal: t.literal.clone(),
            ..Term::default()
        };
        bare(ours).match_with(&bare(theirs), m)
            && actual.len() >= asked.len()
            && asked.iter().zip(actual).all(|(a, b)| a.match_with(b, m))
    }

    fn scientific(&self) -> Option<Scientific> {
        if self.head.as_deref() != Some("OfScientific.ofScientific") || self.implicit {
            return None;
        }
        let args = self.visible_args();
        let [mantissa, sign, exponent] = args.as_slice() else { return None };
        let negative = match sign.head.as_deref()? {
            "Bool.true" => true,
            "Bool.false" => false,
            _ => return None,
        };
        Scientific::from_parts(mantissa.literal.as_deref()?, negative, exponent.literal.as_deref()?)
    }

    pub fn has_numeric_literals(&self) -> bool {
        self.literal
            .as_deref()
            .is_some_and(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
            || self.args.iter().any(Self::has_numeric_literals)
            || self.ty.as_ref().is_some_and(|ty| ty.has_numeric_literals())
    }

    /// The numerals the term asks the values of, as Lean reads them: `0x10`
    /// is `16`, and `2.50` is `2.5`.
    pub fn numerals(&self) -> Vec<String> {
        if let Some(value) = self.scientific() {
            return vec![value.to_string()];
        }
        self.literal
            .iter()
            .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
            .cloned()
            .chain(self.args.iter().flat_map(Self::numerals))
            .chain(self.ty.iter().flat_map(|t| t.numerals()))
            .collect()
    }

    pub fn has_type_constraints(&self) -> bool {
        self.ty.is_some() || self.args.iter().any(Self::has_type_constraints)
    }

    fn base(&self) -> &Term {
        if matches!(self.head.as_deref(), Some("HPow.hPow" | "HMul.hMul")) {
            self.args.first().map_or(self, Self::base)
        } else {
            self
        }
    }

    fn factors<'a>(&'a self, multiplier: u32, out: &mut Vec<(&'a Self, u32)>) -> Option<()> {
        let args = self.visible_args();
        match (self.head.as_deref(), args.as_slice()) {
            (Some("HMul.hMul"), [a, b]) => {
                a.factors(multiplier, out)?;
                b.factors(multiplier, out)
            }
            (Some("HPow.hPow"), [base, exponent]) => base.factors(
                multiplier.checked_mul(exponent.literal.as_ref()?.parse::<u32>().ok()?)?,
                out,
            ),
            _ => {
                out.push((self, multiplier));
                Some(())
            }
        }
    }

    fn match_power(&self, other: &Term, exponent: u32, m: &mut Matching) -> bool {
        let base = self.base();
        let args = other.visible_args();
        if other.head.as_deref() == Some("HPow.hPow") {
            let [factor, exp] = args.as_slice() else { return false };
            let numeral = Term { literal: Some(exponent.to_string()), ..Term::default() };
            return numeral.match_with(exp, m) && base.match_with(factor, m);
        }
        let mut factors = Vec::new();
        if other.factors(1, &mut factors).is_none() {
            return false;
        }
        let total = factors.iter().try_fold(0u32, |n, (_, k)| n.checked_add(*k));
        total == Some(exponent)
            && factors.windows(2).all(|pair| pair[0].0 == pair[1].0)
            && factors.iter().all(|(factor, _)| base.match_with(factor, m))
    }

    /// Unify two specializations of the same parameter, refining wildcards.
    fn merge(&mut self, other: &Term) -> bool {
        for (ours, theirs) in [(&mut self.head, &other.head), (&mut self.literal, &other.literal)] {
            match (ours.as_ref(), theirs) {
                (Some(a), Some(b)) if a != b => return false,
                (None, Some(b)) => *ours = Some(b.clone()),
                _ => {}
            }
        }
        self.args.resize(self.args.len().max(other.args.len()), Self::default());
        self.args.iter_mut().zip(&other.args).all(|(a, b)| a.merge(b))
    }

    /// The constants the term names. Not the heads Lean has no constant for,
    /// `$sort` or [`COERCED`].
    pub fn names(&self) -> Vec<DeclName> {
        self.head
            .iter()
            .filter(|h| !h.starts_with('$'))
            .map(DeclName::new)
            .chain(self.args.iter().flat_map(Self::names))
            .chain(self.ty.iter().flat_map(|t| t.names()))
            .collect()
    }

    pub fn rename(&mut self, from: &str, to: Option<&str>) {
        if self.head.as_deref() == Some(from) {
            self.head = to.map(str::to_string);
        }
        for a in &mut self.args {
            a.rename(from, to);
        }
        if let Some(t) = &mut self.ty {
            t.rename(from, to);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn app(head: &str, args: Vec<Term>) -> Term {
        Term::named(head, args)
    }

    fn var(i: usize) -> Term {
        Term { variable: Some(i), ..Term::default() }
    }

    fn num(n: &str) -> Term {
        Term { literal: Some(n.into()), ..Term::default() }
    }

    fn any() -> Term {
        Term::default()
    }

    fn coe(map: Term, args: Vec<Term>) -> Term {
        app(COERCION, std::iter::once(map).chain(args).collect())
    }

    /// Where `fderiv`'s values are maps, `fderiv 𝕜 f x v w` is the map
    /// `fderiv 𝕜 f x` applied to `v` through one coercion, and what that
    /// returns applied to `w` through another. A pattern without the types
    /// has one, and the numeral is where it is written either way.
    #[test]
    fn a_map_applied_is_one_application_through_every_coercion() {
        let fderiv = |args| app("fderiv", args);
        let row = coe(coe(fderiv(vec![var(0), var(1), var(2)]), vec![var(3)]), vec![num("1")]);
        let once = |v, w| coe(fderiv(vec![any(), any(), any()]), vec![v, w]);
        assert!(once(any(), num("1")).matches(&row));
        assert!(!once(any(), num("2")).matches(&row));
        // And the other way round.
        let flat = coe(fderiv(vec![var(0), var(1), var(2)]), vec![var(3), num("1")]);
        let nested = coe(coe(fderiv(vec![any(), any(), any()]), vec![any()]), vec![num("1")]);
        assert!(nested.matches(&flat));
        // Applied to fewer is another statement.
        let single = coe(fderiv(vec![var(0), var(1), var(2)]), vec![var(3)]);
        assert!(!once(any(), any()).matches(&single));
    }

    /// `↑e x` is applied through whichever coercion the type of `e` has:
    /// `DFunLike.coe` for an `Equiv`, `PartialHomeomorph.toFun'` for a
    /// `PartialHomeomorph`.
    #[test]
    fn a_coercion_written_is_whichever_the_row_applies() {
        let pattern =
            app(COERCED, vec![app(".symm", vec![any()]), app(COERCED, vec![any(), any()])]);
        let equiv = coe(app("Equiv.symm", vec![var(0)]), vec![coe(var(0), vec![var(1)])]);
        let to_fun = |e, x| app("PartialHomeomorph.toFun'", vec![e, x]);
        let own = to_fun(app("PartialHomeomorph.symm", vec![var(0)]), to_fun(var(0), var(1)));
        assert!(pattern.matches(&equiv));
        assert!(pattern.matches(&own));
        assert!(!pattern.matches(&app("Equiv.symm", vec![var(0)])));
        assert_eq!(pattern.names(), [DeclName::new(".symm")]);
    }

    /// The report: `⇑e.symm (e x) = x` ranked `Equiv.symm_apply_apply`
    /// behind 24 statements of `.symm` for one equivalence, as
    /// `Cardinal.preAleph.symm ↑n = ↑n`, which are shorter.
    #[test]
    fn a_row_states_the_pattern_or_a_particular_case_of_it() {
        let applied = Term { args: vec![any()], ..Term::default() };
        let pattern = app("Eq", vec![coe(app(".symm", vec![any()]), vec![applied]), any()]);
        let general = app(
            "Eq",
            vec![coe(app("Equiv.symm", vec![var(0)]), vec![coe(var(0), vec![var(1)])]), var(1)],
        );
        assert_eq!(pattern.specifics(&general), Some(0));
        let cast = || app("Nat.cast", vec![var(0)]);
        let aleph = app("Cardinal.preAleph", Vec::new());
        let particular = app("Eq", vec![coe(app("Equiv.symm", vec![aleph]), vec![cast()]), cast()]);
        assert_eq!(pattern.specifics(&particular), Some(3));
        let other = app("Eq", vec![coe(app("Equiv.trans", vec![var(0)]), vec![var(1)]), var(1)]);
        assert_eq!(pattern.specifics(&other), None);
    }
}
