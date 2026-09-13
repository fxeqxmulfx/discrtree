//! `dt find` — shape search, the main mode, plus `dt dup`.

use crate::application::ports::{DeclRepo, SourceFiles};
use crate::domain::decl::Decl;
use crate::domain::lean_text;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::query::{self, Query};
use crate::domain::source::SourceId;
use crate::error::{Result, bail};
use std::path::Path;

pub struct Find<'a> {
    pub repo: &'a dyn DeclRepo,
}

/// What a search found, and whether the limit hid anything.
///
/// The flag is the cheaper half of the answer: it lets the caller tell
/// "these are all the matches" from "these are the best few of many", which
/// otherwise costs a second search with a larger limit.
#[derive(Debug)]
pub struct Hits {
    pub rows: Vec<Decl>,
    pub truncated: bool,
}

impl Find<'_> {
    pub fn run(&self, query: &Query) -> Result<Hits> {
        if query.is_empty() {
            bail!(
                "nothing to search for: give a pattern, or one of --name, --concl, --uses, --in, --text"
            )
        }
        let mut rows = self.repo.find(query)?;
        rows.sort_by_key(|d| query::rank(query, d));
        let truncated = rows.len() > query.limit;
        rows.truncate(query.limit);
        Ok(Hits { rows, truncated })
    }
}

/// One local declaration and what upstream already has that looks like it.
pub struct Duplicate {
    pub local: Decl,
    pub candidates: Vec<Scored>,
}

pub struct Scored {
    pub decl: Decl,
    /// Overlap of the two constant sets, in `0.0..=1.0`.
    pub similarity: f32,
}

/// `dt dup <file>` — is this already in Mathlib?
///
/// The comparison is over the constants a statement mentions, not over its
/// text: two statements of the same fact rarely agree on binder names and
/// almost always agree on which constants they are about.
pub struct Dup<'a> {
    pub repo: &'a dyn DeclRepo,
    pub files: &'a dyn SourceFiles,
    /// The source the file belongs to, so its own rows are not reported as
    /// duplicates of themselves.
    pub local: SourceId,
    /// How much overlap is worth reporting.
    pub threshold: f32,
}

impl Dup<'_> {
    /// `file` is the path as the user typed it; `module` is what it is called
    /// once built.
    pub fn run(&self, file: &Path, module: &ModuleName) -> Result<Vec<Duplicate>> {
        let text = std::fs::read_to_string(file)
            .map_err(|e| crate::error::Error::new(format!("{}: {e}", file.display())))?;
        let mut out = Vec::new();
        for scanned in lean_text::scan(&text) {
            // Prefer the indexed row: it has an elaborated type and real
            // constants. Fall back to what the scanner saw.
            let local = match self.repo.get(&scanned.name)? {
                Some(d) => d,
                None => {
                    let mut d =
                        Decl::stub(scanned.name.as_str(), self.local.as_str(), module.as_str());
                    d.ty = scanned.statement.clone();
                    // Only identifiers the index knows. The scanner also sees
                    // notation (`\u{211d}`) and projections (`.mpr`), and since the
                    // conditions combine with AND, one identifier that is not a
                    // constant would guarantee no candidates at all.
                    d.consts = self.known(&scanned.idents)?;
                    d.elaborated = false;
                    d
                }
            };
            if !local.kind.is_proposition() || local.consts.is_empty() {
                continue;
            }
            let candidates = self.candidates(&local)?;
            if !candidates.is_empty() {
                out.push(Duplicate { local, candidates });
            }
        }
        Ok(out)
    }

    /// The identifiers that name something the index has heard of.
    fn known(&self, idents: &[DeclName]) -> Result<Vec<DeclName>> {
        let mut out = Vec::new();
        for i in idents {
            if self.repo.contains(i)? {
                out.push(i.clone());
            }
        }
        Ok(out)
    }

    fn candidates(&self, local: &Decl) -> Result<Vec<Scored>> {
        // The conclusion head alone is not evidence: `True`, `Eq` and `LE.le`
        // each describe a large fraction of any corpus, so a statement with no
        // distinctive constant left has nothing to be compared against and
        // reporting matches for it would be noise, not a duplicate.
        let uses = distinctive(&local.consts);
        if uses.is_empty() {
            return Ok(Vec::new());
        }
        let mut q = Query::new();
        q.shape.concl = local.shape.concl.clone();
        q.uses = uses;
        q.elaborated_only = true;
        q.no_sorry = true;
        q.limit = 200;
        let mut scored: Vec<Scored> = self
            .repo
            .find(&q)?
            .into_iter()
            .filter(|d| d.source != self.local && d.name != local.name)
            .map(|d| {
                let similarity = jaccard(&local.consts, &d.consts);
                Scored { decl: d, similarity }
            })
            .filter(|s| s.similarity >= self.threshold)
            .collect();
        scored.sort_by(|a, b| b.similarity.total_cmp(&a.similarity));
        scored.truncate(5);
        Ok(scored)
    }
}

/// Constants worth anchoring a search on: the structural ones (`Eq`, `LE.le`,
/// `And`) match half of Mathlib and only slow the query down.
fn distinctive(consts: &[DeclName]) -> Vec<DeclName> {
    const UBIQUITOUS: &[&str] = &[
        "Eq",
        "Iff",
        "And",
        "Or",
        "Not",
        "LE.le",
        "LT.lt",
        "Membership.mem",
        "HAdd.hAdd",
        "HMul.hMul",
        "HSub.hSub",
        "HDiv.hDiv",
        "OfNat.ofNat",
        "Zero.zero",
        "One.one",
        "Nat",
        "Prop",
        "Type",
        "Sort",
        "Exists",
        "Set",
        "Subtype",
        "Function.comp",
        // A statement that says only `True` is a placeholder. Anchoring on it
        // proposes `True.intro` and `trivial` as what the project meant.
        "True",
        "False",
        "trivial",
    ];
    let mut v: Vec<DeclName> =
        consts.iter().filter(|c| !UBIQUITOUS.contains(&c.as_str())).cloned().collect();
    // Three conditions are enough to make the query selective; more of them
    // only rules out the paraphrase that spells one constant differently.
    v.truncate(3);
    v
}

/// Overlap of the two constant sets. Deduplicated first: a scanned statement
/// repeats a constant as often as it is written, and counting those repeats
/// gives a "similarity" above 1.
fn jaccard(a: &[DeclName], b: &[DeclName]) -> f32 {
    let a: std::collections::BTreeSet<&DeclName> = a.iter().collect();
    let b: std::collections::BTreeSet<&DeclName> = b.iter().collect();
    if a.is_empty() || b.is_empty() {
        return 0.0;
    }
    let shared = a.intersection(&b).count();
    shared as f32 / (a.len() + b.len() - shared) as f32
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(v: &[&str]) -> Vec<DeclName> {
        v.iter().map(|s| DeclName::new(*s)).collect()
    }

    #[test]
    fn structural_constants_never_anchor_a_search() {
        let got = distinctive(&names(&["Eq", "LE.le", "Real.exp", "Finset.sum"]));
        assert_eq!(got, names(&["Real.exp", "Finset.sum"]));
    }

    #[test]
    fn similarity_is_set_overlap_not_order() {
        assert_eq!(jaccard(&names(&["a", "b"]), &names(&["b", "a"])), 1.0);
        assert_eq!(jaccard(&names(&["a", "b"]), &names(&["c"])), 0.0);
        assert_eq!(jaccard(&names(&["a", "b"]), &names(&["b", "c"])), 1.0 / 3.0);
        assert_eq!(jaccard(&[], &names(&["a"])), 0.0);
    }

    #[test]
    fn a_repeated_constant_cannot_push_similarity_above_one() {
        // `∀ x, True ∧ True` mentions `True` twice; counting both made a
        // duplicate report itself as 200% similar.
        assert_eq!(jaccard(&names(&["True", "True"]), &names(&["True"])), 1.0);
        assert!(jaccard(&names(&["a", "a", "b"]), &names(&["a"])) <= 1.0);
    }

    #[test]
    fn a_placeholder_statement_anchors_on_nothing() {
        assert!(distinctive(&names(&["True"])).is_empty());
    }
}
