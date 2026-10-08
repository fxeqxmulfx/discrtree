//! Positioned types and numeric literals, matched against expressions read by Lean.

use crate::domain::name::DeclName;
use crate::domain::numeral::Scientific;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

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
        self.match_with(other, &mut BTreeMap::new())
    }

    fn match_with(&self, other: &Term, assigned: &mut BTreeMap<usize, Term>) -> bool {
        if let Some(ty) = &self.ty
            && !other.ty.as_ref().is_some_and(|actual| ty.match_with(actual, assigned))
        {
            return false;
        }
        if self.head.is_none() && self.literal.is_none() && self.args.is_empty() {
            return true;
        }
        // Telescope parameters may be specialized, consistently across every
        // occurrence. `α` cannot be both Nat and Int in one answer.
        if let Some(var) = other.variable {
            let mut value = self.clone();
            value.ty = None;
            if !other.args.is_empty() {
                value.args.clear();
            }
            let consistent = match assigned.get_mut(&var) {
                Some(previous) => previous.merge(&value),
                None => {
                    assigned.insert(var, value);
                    true
                }
            };
            if other.args.is_empty() {
                return consistent;
            }
            let args = other.visible_args();
            return consistent
                && self.args.len() == args.len()
                && self
                    .args
                    .iter()
                    .zip(args)
                    .all(|(asked, actual)| asked.match_with(actual, assigned));
        }
        if let Some(exponent) = self.power
            && self.head != other.head
            && matches!(other.head.as_deref(), Some("HPow.hPow" | "HMul.hMul"))
        {
            return self.match_power(other, exponent, assigned);
        }
        if let Some(head) = &self.head
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
            && self.args.iter().zip(args).all(|(asked, actual)| asked.match_with(actual, assigned))
    }

    fn visible_args(&self) -> Vec<&Term> {
        match &self.explicit {
            Some(indices) => indices.iter().filter_map(|i| self.args.get(*i)).collect(),
            None => self.args.iter().collect(),
        }
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

    fn match_power(
        &self,
        other: &Term,
        exponent: u32,
        assigned: &mut BTreeMap<usize, Term>,
    ) -> bool {
        let base = self.base();
        let args = other.visible_args();
        if other.head.as_deref() == Some("HPow.hPow") {
            let [factor, exp] = args.as_slice() else { return false };
            let numeral = Term { literal: Some(exponent.to_string()), ..Term::default() };
            return numeral.match_with(exp, assigned) && base.match_with(factor, assigned);
        }
        let mut factors = Vec::new();
        if other.factors(1, &mut factors).is_none() {
            return false;
        }
        let total = factors.iter().try_fold(0u32, |n, (_, k)| n.checked_add(*k));
        total == Some(exponent)
            && factors.windows(2).all(|pair| pair[0].0 == pair[1].0)
            && factors.iter().all(|(factor, _)| base.match_with(factor, assigned))
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

    pub fn names(&self) -> Vec<DeclName> {
        self.head
            .iter()
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
