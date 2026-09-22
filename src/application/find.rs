//! `dt find` — shape search, the main mode, plus `dt dup`.

use crate::application::ports::{Build, DeclRepo, Missing, SourceFiles};
use crate::domain::decl::{ArgHead, Decl, DeclKind, Shape};
use crate::domain::lean_text;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::pattern;
use crate::domain::query::{self, Power, Query};
use crate::domain::source::SourceId;
use crate::error::{Result, bail};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

/// How many rows a diagnosis reads to see how answers spread, rather than the
/// best few: wide enough to show a spread, narrow enough that a condition
/// matching half the corpus does not pay for a full scan.
const SPREAD: usize = 60;

pub struct Find<'a> {
    pub repo: &'a dyn DeclRepo,
    /// Consulted only when a search came back empty, to tell a module prefix
    /// that is wrong from one that was never indexed.
    pub build: &'a dyn Build,
}

/// Why a search came back empty. The three cases need different repairs, and
/// telling them apart from outside costs another search each.
#[derive(Debug, PartialEq, Eq)]
pub enum Empty {
    /// A single condition matched nothing. There is nothing left to say: the
    /// condition that failed is the one that was asked.
    Plain,
    /// These conditions match nothing in the index even on their own — a
    /// misspelled constant, a module prefix that is not a prefix. Edit them.
    Barren(Vec<String>),
    /// Every condition matches something; no row satisfies all of them, and
    /// the query narrowed nothing. Drop one rather than correcting any.
    Combination,
    /// The query narrowed where it looked -- `--in`, `--source` -- and that
    /// scope holds declarations: `held` of them. What emptied the search is
    /// one of the conditions asked inside it, and the scope is the one thing
    /// not to touch.
    ///
    /// Told apart from `Combination` because "drop one" picks the condition
    /// whose removal yields the most rows, and that is the narrowing one
    /// nearly every time -- which maximises rows and blames intent. A reader
    /// who writes `--in Transformer.ALM` is saying where the answer belongs;
    /// `--name addr` is the guess. Naming the scope and its size says which
    /// half was right.
    InScope {
        /// The module prefix as it was written, not resolved to a module: it
        /// is a prefix, and what it stands for is a scope rather than a name.
        module: Option<String>,
        source: Option<SourceId>,
        /// Declarations in the scope, counted rather than listed.
        held: usize,
        /// The conditions that match nothing inside the scope, in the words
        /// they were written. Empty when each of them matches there and only
        /// their combination does not.
        failing: Vec<String>,
        /// Where the rows that satisfy every condition *but* the scope live,
        /// commonest module first. Empty when dropping it still matches
        /// nothing.
        ///
        /// The reader may have guessed wrong after all, and this is the whole
        /// of what they would need then: `div_le_div_iff` is not in
        /// `Mathlib.Algebra.Order.Field`, it is in
        /// `Mathlib.Algebra.Order.GroupWithZero.Basic`.
        elsewhere: Vec<(ModuleName, usize)>,
    },
    /// The search was asked about a corpus the build can import and no source
    /// indexes. Neither repair above applies: nothing is misspelled and no
    /// condition needs dropping, the corpus was never dumped. Told apart from
    /// `Barren` because they look identical from the index and lead opposite
    /// ways — one says edit the flag, and editing the flag here can only
    /// produce another empty answer.
    NotIndexed { asked: Asked, missing: Missing },
    /// `--kind instance` against an index whose elaborated rows have no
    /// instances in them at all. `instance` is an attribute Lean hangs on a
    /// `def`, and a dump written before `dt` read that attribute recorded
    /// every instance as `def` -- so the flag is right, the index is old, and
    /// the repair is a re-dump rather than an edit to the query.
    InstancesAreDefs,
    /// The pattern is the whole of why the search failed: on its own, with
    /// every other condition dropped, it still matches nothing, and each
    /// constant in it is in the index.
    ///
    /// "Drop one condition" is an answer about flags, and a pattern is one
    /// thing to whoever wrote it however many conditions it becomes here.
    /// `Real.log _ ≤ Real.sqrt _` has nothing to drop; what it has is three
    /// near misses worth checking, and the search that failed already paid for
    /// most of the work of checking them.
    NoSuchShape {
        /// Conclusion heads whose statements do take these arguments,
        /// commonest first. The common near miss: the right two sides under
        /// the wrong relation.
        under: Vec<(DeclName, usize)>,
        /// Argument heads that match once the others are written `_`. Empty
        /// unless the pattern named at least two, where it is the difference
        /// between "this constant is never an argument here" and "these
        /// constants are never arguments together".
        without: Vec<DeclName>,
        /// The same arguments in the other order match.
        swapped: bool,
    },
    /// The pattern's shape matches, and these constants, also written in the
    /// pattern, are mentioned by nothing of that shape.
    ///
    /// `List.range' _ _ _ ++ List.range' _ _ _ = _` is four conditions inside
    /// and one to whoever wrote it, and "drop one" names no flag they gave.
    NotInShape {
        absent: Vec<DeclName>,
        /// No one of them is missing on its own; only all of them at once.
        together: bool,
    },
    /// `--name` names a declaration outright, and its conclusion is not the
    /// pattern's.
    ///
    /// `dt find 'List.Sublist _ _' --name sublist_cons_iff`: the lemma is an
    /// `Iff` with a `Sublist` on one side, the pattern is matched against the
    /// whole conclusion, and no flag is worth dropping. The row is in hand, so
    /// the answer is what it says.
    NamedElsewise {
        name: DeclName,
        shape: Shape,
        /// The pattern's conclusion head is one of that conclusion's arguments:
        /// the pattern describes a side of it.
        on_a_side: bool,
    },
    /// Something matches, and all of it is what the compiler generated, which
    /// `find` hides unless asked.
    OnlyGenerated,
    /// A bare word in the pattern is the last component of constants the index
    /// does hold, and none of them answered either. `export Inner (inner)`
    /// makes Lean print `inner` for `Inner.inner`, so a pattern copied back out
    /// of a goal is spelled the way it printed rather than the way it is
    /// stored -- and "matches nothing on its own" would send the reader to
    /// correct a word that is not misspelled.
    Unqualified { written: String, candidates: Vec<DeclName> },
}

/// Which condition led outside the index, as it was written.
///
/// Two of them, because what can honestly be said differs. A module prefix
/// belongs to a corpus outright; a name only says its namespace does, and only
/// when it has one — `--name add_one_le_iff` is unqualified, has no namespace
/// to read, and gets no note rather than a guessed one.
#[derive(Debug, PartialEq, Eq)]
pub enum Asked {
    /// `--in`, as written.
    Module(String),
    /// `--name`, when what was written was a qualified name.
    Name(DeclName),
}

impl Asked {
    /// The condition as the reader typed it.
    pub fn as_str(&self) -> &str {
        match self {
            Asked::Module(m) => m,
            Asked::Name(n) => n.as_str(),
        }
    }
}

/// What a search found, and the two things about it a caller would otherwise
/// have to spend another search to learn.
///
/// `truncated` tells "these are all the matches" from "these are the best few
/// of many". `empty` says which repair an empty result needs. Both are nearly
/// free here and cost a round trip to discover from outside, which is the
/// expensive kind of waste.
#[derive(Debug)]
pub struct Hits {
    pub rows: Vec<Decl>,
    pub truncated: bool,
    /// `None` when something matched.
    pub empty: Option<Empty>,
    /// What a bare word in the pattern was read as, when the rows answer the
    /// pattern read that way. Reported rather than applied silently: the rows
    /// below answer a question spelled differently from the one that was
    /// asked.
    pub read_as: Vec<(String, DeclName)>,
    /// Words of the pattern read as variables on that second look, for the
    /// same reason. See [`Reading::variables`].
    pub variables: Vec<String>,
    /// `--text` words searched for as `--uses` instead, for the same reason:
    /// a constant's name, which a type prints as its notation. `Finset.sum`
    /// is `∑ i ∈ s, f i` in every statement about it, and only a docstring
    /// spells it out.
    pub text_as_uses: Vec<String>,
    /// Whether the rows state the pattern's relation with its two sides the
    /// other way round, for the same reason. Only a relation that reads the
    /// same both ways is turned: a lemma stating `b = a` answers `a = b` with
    /// one `.symm`, and one stating `b ≤ a` answers nothing about `a ≤ b`.
    pub swapped: bool,
    /// The powers the pattern wrote, as it wrote them, when the rows write
    /// them the other way, for the same reason. `sq_nonneg` is about `a ^ 2`
    /// and `mul_self_nonneg` about `a * a`, and whoever writes either means
    /// both. See [`Power`].
    pub respelled: Vec<Power>,
}

/// The relations whose two sides can trade places without changing what a
/// lemma says, as a reader uses it.
const SYMMETRIC: &[&str] = &["Eq", "Iff", "Ne"];

/// The query with the two sides of its relation traded, where the relation
/// is one of [`SYMMETRIC`] and trading them changes the question.
fn turned(query: &Query) -> Option<Query> {
    let shape = &query.shape;
    let symmetric = shape.concl.as_ref().is_some_and(|c| SYMMETRIC.contains(&c.as_str()));
    if !symmetric || shape.args.len() != 2 || shape.args[0] == shape.args[1] {
        return None;
    }
    let mut out = query.clone();
    out.shape.args.reverse();
    // A power stays with the side it is written on.
    for (i, _) in &mut out.powers {
        *i = 1 - *i;
    }
    Some(out)
}

/// The query asked with the powers its pattern writes spelled the other way:
/// all of them first, then each on its own where there are more. Each comes
/// with the powers as the pattern wrote them, which is what the reader is
/// told was traded.
///
/// A power is traded where the shape has its head, which is where the pattern
/// wrote it; one further down is a constant of the statement and no argument
/// of the shape, and is not asked about again.
fn respellings(query: &Query) -> Vec<(Query, Vec<Power>)> {
    let traded: Vec<usize> = (0..query.powers.len())
        .filter(|&j| {
            let (i, p) = query.powers[j];
            query.shape.args.get(i) == Some(&ArgHead::Named(p.head()))
        })
        .collect();
    let mut sets = vec![traded.clone()];
    if traded.len() > 1 {
        sets.extend(traded.iter().map(|&j| vec![j]));
    }
    sets.into_iter()
        .filter(|set| !set.is_empty())
        .map(|set| {
            let mut out = query.clone();
            let mut written = Vec::new();
            for j in set {
                let (i, p) = query.powers[j];
                out.shape.args[i] = ArgHead::Named(p.respelled().head());
                out.powers[j] = (i, p.respelled());
                written.push(p);
            }
            written.sort();
            written.dedup();
            (out, written)
        })
        .collect()
}

/// Whether the statement writes each power the query does, spelled the way
/// the query spells it, on the side the query has it. The index keys on heads
/// and has `HMul.hMul` for `x * x` and for `x * y` alike: without this, a
/// square asked for as a product would be answered by every product.
fn writes_powers(query: &Query, d: &Decl) -> bool {
    let has = pattern::powers_in(&d.ty);
    query.powers.iter().all(|p| has.contains(p))
}

/// What the words of a pattern that found nothing were read as, the second
/// time.
#[derive(Debug, Default)]
struct Reading {
    /// Each bare word Lean prints for a constant, and the constants it could
    /// be, commonest first.
    called: Vec<(String, Vec<DeclName>)>,
    /// Words in lower case that name nothing: no row is called that, mentions
    /// it, or prints it for a constant of another name.
    ///
    /// Asked of the index, where a single letter is a variable by its
    /// spelling alone (see `pattern::is_variable`). A letter is never a
    /// constant worth searching for; a word may be -- `deriv`, `id`,
    /// `closure` -- and so may one Lean exports, and the index is the one
    /// thing that knows which words are neither. That is also why this is a
    /// second look: a pattern that answered as written is read as written, in
    /// every project alike.
    variables: Vec<String>,
}

/// The query with each bare word replaced by the constant it most likely
/// names, and each word read as a variable made `_`. `None` when there was
/// nothing to replace.
fn qualified(query: &Query, reading: &Reading) -> Option<Query> {
    let top = |n: &DeclName| {
        reading.called.iter().find(|(w, _)| w == n.as_str()).and_then(|(_, c)| c.first()).cloned()
    };
    let variable = |n: &DeclName| reading.variables.iter().any(|v| v == n.as_str());
    let mut out = query.clone();
    let mut any = false;
    if let Some(c) = &out.shape.concl {
        if let Some(resolved) = top(c) {
            out.shape.concl = Some(resolved);
            any = true;
        } else if variable(c) {
            out.shape.concl = None;
            any = true;
        }
    }
    for a in &mut out.shape.args {
        if let ArgHead::Named(n) = a {
            if let Some(resolved) = top(n) {
                *a = ArgHead::Named(resolved);
                any = true;
            } else if variable(n) {
                *a = ArgHead::Any;
                any = true;
            }
        }
    }
    // A constant inside the pattern is in both lists, and is renamed in both so
    // that a failure still blames it as written in the pattern.
    for u in out.uses.iter_mut().chain(out.pattern_uses.iter_mut()) {
        if let Some(resolved) = top(u) {
            *u = resolved;
            any = true;
        }
    }
    let written = out.pattern_uses.clone();
    let before = out.uses.len();
    out.uses.retain(|u| !(variable(u) && written.contains(u)));
    out.pattern_uses.retain(|u| !variable(u));
    any |= out.uses.len() != before;
    any.then_some(out)
}

impl Find<'_> {
    pub fn run(&self, query: &Query) -> Result<Hits> {
        if query.is_empty() {
            bail!(
                "nothing to search for: give a pattern, or one of --name, --concl, --uses, --in, --text"
            )
        }
        let mut rows = self.repo.find(query)?;
        // What the query is ranked and truncated by: the one that found the
        // rows, which is not the one that was typed when a bare word had to be
        // resolved first.
        let mut asked = query.clone();
        let mut reading = Reading::default();
        let mut resolved = false;
        if rows.is_empty() {
            reading = self.resolve(query)?;
            // Kept when it finds nothing too, so that the looks below are
            // taken at the words as the index spells them: `inner ℝ _ _ ^ 2 ≤
            // _` needs `inner` read as `Inner.inner` and its square written as
            // a product before anything answers.
            if let Some(retry) = qualified(query, &reading) {
                rows = self.repo.find(&retry)?;
                asked = retry;
                resolved = true;
            }
        }
        let mut text_as_uses = Vec::new();
        if rows.is_empty() && !asked.text.is_empty() {
            let mut retry = asked.clone();
            for t in &asked.text {
                let name = DeclName::new(t.as_str());
                // Dotted, so that a word like `exp` or `id` -- a constant, and
                // also a word a docstring means as a word -- stays text.
                if t.contains('.') && self.repo.is_constant(&name)? {
                    text_as_uses.push(t.clone());
                    retry.uses.push(name);
                }
            }
            retry.text.retain(|t| !text_as_uses.contains(t));
            if !text_as_uses.is_empty() {
                let found = self.repo.find(&retry)?;
                match found.is_empty() {
                    true => text_as_uses.clear(),
                    false => (rows, asked) = (found, retry),
                }
            }
        }
        let mut swapped = false;
        if rows.is_empty()
            && let Some(retry) = turned(&asked)
        {
            let found = self.repo.find(&retry)?;
            if !found.is_empty() {
                (rows, asked, swapped) = (found, retry, true);
            }
        }
        let mut respelled = Vec::new();
        if rows.is_empty() {
            'respelt: for (retry, written) in respellings(&asked) {
                let turn = turned(&retry).map(|t| (t, true));
                for (retry, turn) in std::iter::once((retry, false)).chain(turn) {
                    let mut found = self.repo.find(&retry)?;
                    found.retain(|d| writes_powers(&retry, d));
                    if !found.is_empty() {
                        (rows, asked, swapped, respelled) = (found, retry, turn, written);
                        break 'respelt;
                    }
                }
            }
        }
        // A variable is reported whatever was found: with no constant to
        // blame, the question left to diagnose is the one without the
        // variables in it. A constant is reported when the rows answer it, and
        // otherwise what is diagnosed is the pattern as it was written, whose
        // word it is that the reader is told about.
        let stands = resolved && (!rows.is_empty() || reading.called.is_empty());
        let (read_as, variables) = match stands {
            true => (
                reading
                    .called
                    .iter()
                    .filter_map(|(w, c)| c.first().map(|n| (w.clone(), n.clone())))
                    .collect(),
                reading.variables.clone(),
            ),
            false => (Vec::new(), Vec::new()),
        };
        if resolved && !stands {
            asked = query.clone();
        }
        rows.sort_by_key(|d| query::rank(&asked, d));
        let truncated = rows.len() > asked.limit;
        rows.truncate(asked.limit);
        let empty = match rows.is_empty() {
            true => Some(self.diagnose(&asked, &reading.called)?),
            false => None,
        };
        Ok(Hits { rows, truncated, empty, read_as, variables, text_as_uses, swapped, respelled })
    }

    /// The constants each bare word in the pattern could be naming, commonest
    /// first, for the words that name any; and the words in lower case that
    /// name nothing, as variables.
    ///
    /// Every word of the pattern, not only its heads: `export Bool (false
    /// true)` drops the namespace wherever the printer meets the constant, and
    /// `List.count false l` is copied back with `false` an argument of an
    /// argument. Counted as heads all the same, because that is the count the
    /// index keeps cheaply, and the constant a word names somewhere inside a
    /// statement is the one it names at the top of others.
    ///
    /// Asked only of a search that found nothing: a word that answered as
    /// written is a word that meant what it said, and resolving it anyway
    /// would be two scans of the index to change nothing.
    fn resolve(&self, query: &Query) -> Result<Reading> {
        let mut out = Reading::default();
        let mut seen: Vec<&str> = Vec::new();
        for word in query.shape.heads().chain(&query.pattern_uses) {
            // A word written twice -- `exp _ ≤ exp _` -- is one word to
            // resolve and one line to report.
            if word.as_str().contains('.') || seen.contains(&word.as_str()) {
                continue;
            }
            seen.push(word.as_str());
            // A word the index has by that spelling means what it says. `Eq`
            // is spelled `Eq` there, and `deriv` is `deriv` however many
            // namespaces have one of their own; a query that failed with it in
            // the pattern failed for some other reason.
            if self.repo.is_constant(word)? {
                continue;
            }
            let called = self.repo.heads_called(word.as_str())?;
            if !called.is_empty() {
                out.called.push((word.as_str().to_owned(), called));
            } else if word.as_str().starts_with(char::is_lowercase) {
                out.variables.push(word.as_str().to_owned());
            }
        }
        Ok(out)
    }

    /// Ask each condition on its own. One row each, so the diagnosis costs
    /// about as much as the search that failed.
    fn diagnose(&self, query: &Query, called: &[(String, Vec<DeclName>)]) -> Result<Empty> {
        // First, because it is the only diagnosis about the words themselves:
        // every other one takes the query at its word and reports what the
        // index said about it.
        if let Some((written, candidates)) = called.first() {
            return Ok(Empty::Unqualified {
                written: written.clone(),
                candidates: candidates.clone(),
            });
        }
        // Hidden rather than absent: the rows are there, and the flag that
        // shows them is the whole repair.
        if !query.generated
            && !self.repo.find(&Query { generated: true, limit: 1, ..query.clone() })?.is_empty()
        {
            return Ok(Empty::OnlyGenerated);
        }
        // A module prefix is the one condition that can fail for a reason no
        // probe can see. Every other empty answer means the index was asked and
        // said no; this one means the index was never told. The build is asked
        // first because it costs no query at all, and in a project whose
        // sources cover every package it answers `None` immediately.
        if let Some(m) = &query.module
            && let Some(missing) = self.build.module(m)
            && self
                .repo
                .find(&Query { module: Some(m.clone()), limit: 1, ..Query::new() })?
                .is_empty()
        {
            return Ok(Empty::NotIndexed { asked: Asked::Module(m.clone()), missing });
        }
        // And the same for a name that carries its namespace. `--name` is a
        // substring search, so most of what is passed to it is a fragment with
        // nothing to read; a qualified name is the case where the reader
        // already knows what they are looking for, which is also the case where
        // `no match` is most readily believed to mean the lemma does not exist.
        if let Some(n) = &query.name
            && n.contains('.')
            && let Some(missing) = self.build.declaring(n)
            && self
                .repo
                .find(&Query { name: Some(n.clone()), limit: 1, ..Query::new() })?
                .is_empty()
        {
            return Ok(Empty::NotIndexed { asked: Asked::Name(DeclName::new(n.clone())), missing });
        }
        // Asked before the conditions are probed, because `--kind instance`
        // does match on its own -- text rows have carried the kind since the
        // scanner was written -- and the answer would otherwise be "drop a
        // condition", which is the one repair that cannot help here.
        if query.kind == [DeclKind::Instance]
            && self
                .repo
                .find(&Query {
                    kind: vec![DeclKind::Instance],
                    elaborated_only: true,
                    limit: 1,
                    ..Query::new()
                })?
                .is_empty()
        {
            return Ok(Empty::InstancesAreDefs);
        }
        let mut conditions = query.conditions();
        if conditions.len() < 2 {
            // Still worth naming when the condition reads less than its flag
            // suggests: "matches nothing" from `--uses` reads as "nothing uses
            // it", and the renderer has a line to add about that.
            return Ok(match conditions.pop() {
                Some((label, _))
                    if label.starts_with("--uses ") || label.starts_with("--text ") =>
                {
                    Empty::Barren(vec![label])
                }
                _ => Empty::Plain,
            });
        }
        let mut barren = Vec::new();
        for (label, probe) in conditions {
            if self.repo.find(&probe)?.is_empty() {
                barren.push(label);
            }
        }
        if !barren.is_empty() {
            return Ok(Empty::Barren(barren));
        }
        // Before "drop one", because when the shape fails on its own there is
        // no other condition whose dropping would help, and the conditions a
        // pattern was taken apart into are not ones the reader can drop.
        if !query.shape.is_empty() && self.shape_fails_alone(query)? {
            return self.no_such_shape(&query.shape);
        }
        // The same, one step out: the shape matches, and what else the pattern
        // names is what nothing of that shape mentions. Still not "drop one" --
        // with no flags given, the only conditions are the pattern's own.
        if !query.pattern_uses.is_empty()
            && let Some(empty) = self.absent_from_shape(query)?
        {
            return Ok(empty);
        }
        if let Some(empty) = self.named_elsewise(query)? {
            return Ok(empty);
        }
        if let Some(empty) = self.inside_scope(query)? {
            return Ok(empty);
        }
        Ok(Empty::Combination)
    }

    /// What a search that said where to look reports when the place it named
    /// is populated: the scope, its size, and which of the other conditions
    /// found nothing in it.
    ///
    /// `None` when the query narrowed nothing, or when the scope is empty --
    /// and an empty scope is already `Barren`, which says to correct it.
    fn inside_scope(&self, query: &Query) -> Result<Option<Empty>> {
        if query.module.is_none() && query.source.is_none() {
            return Ok(None);
        }
        // The scope as the search would see it, generated names included or
        // not as the query asks: a count the reader cannot reproduce is worse
        // than no count.
        let scope = Query {
            module: query.module.clone(),
            source: query.source.clone(),
            generated: query.generated,
            ..Query::new()
        };
        let held = self.repo.count(&scope)?;
        if held == 0 {
            return Ok(None);
        }
        let rest: Vec<(String, Query)> = query
            .conditions()
            .into_iter()
            .filter(|(label, _)| !(label.starts_with("--in ") || label.starts_with("--source ")))
            .collect();
        // One condition beside the scope is the one that emptied it: the
        // search just ran it inside the scope and it found nothing. Probing
        // it again would repeat the whole query to learn what is known.
        let mut failing: Vec<String> = rest.iter().map(|(l, _)| l.clone()).collect();
        if rest.len() > 1 {
            failing.clear();
            for (label, probe) in rest {
                let inside = Query {
                    module: scope.module.clone(),
                    source: scope.source.clone(),
                    generated: query.generated,
                    // The probe asks whether anything matches, not what does.
                    limit: 1,
                    ..probe
                };
                if self.repo.find(&inside)?.is_empty() {
                    failing.push(label);
                }
            }
        }
        Ok(Some(Empty::InScope {
            module: query.module.clone(),
            source: query.source.clone(),
            held,
            failing,
            elsewhere: self.elsewhere(query)?,
        }))
    }

    /// The declaration `--name` names outright, when it is there and the
    /// pattern does not fit it.
    ///
    /// Asked last of the pattern's diagnoses, and only of a name that is a
    /// whole name or a whole last component: a fragment finds many rows, and
    /// "`--name sublist` finds `List.sublist_cons_iff`" would be a guess at
    /// which of them was meant.
    fn named_elsewise(&self, query: &Query) -> Result<Option<Empty>> {
        let Some(n) = &query.name else { return Ok(None) };
        if query.shape.is_empty() {
            return Ok(None);
        }
        let both =
            Query { name: Some(n.clone()), shape: query.shape.clone(), limit: 1, ..Query::new() };
        if !self.repo.find(&both)?.is_empty() {
            return Ok(None);
        }
        let by_name = Query { name: Some(n.clone()), limit: SPREAD, ..Query::new() };
        let asked = n.to_lowercase();
        let found = self.repo.find(&by_name)?.into_iter().filter(|d| d.shaped()).find(|d| {
            d.name.as_str().to_lowercase() == asked || d.name.base().to_lowercase() == asked
        });
        Ok(found.map(|d| {
            let on_a_side = query.shape.concl.as_ref().is_some_and(|c| {
                d.shape.args.iter().any(|a| matches!(a, ArgHead::Named(x) if c.names(x)))
            });
            Empty::NamedElsewise { name: d.name, shape: d.shape, on_a_side }
        }))
    }

    /// Whether the pattern, with every flag dropped, still matches nothing.
    fn shape_fails_alone(&self, query: &Query) -> Result<bool> {
        let bare = Query { shape: query.shape.clone(), limit: 1, ..Query::new() };
        // `Query` compares its conditions and nothing else, so this is "the
        // pattern was the whole query" -- and then the search that already
        // failed was the probe.
        if bare == *query {
            return Ok(true);
        }
        Ok(self.repo.find(&bare)?.is_empty())
    }

    /// The constants written in the pattern that nothing of its shape
    /// mentions, when the pattern on its own matches nothing. Each on its own
    /// where some fail that way; all of them where only the set does.
    fn absent_from_shape(&self, query: &Query) -> Result<Option<Empty>> {
        let with = |uses: Vec<DeclName>| Query {
            shape: query.shape.clone(),
            uses,
            pattern_uses: query.pattern_uses.clone(),
            limit: 1,
            ..Query::new()
        };
        let whole = with(query.pattern_uses.clone());
        if whole != *query && !self.repo.find(&whole)?.is_empty() {
            return Ok(None);
        }
        let mut absent = Vec::new();
        if query.pattern_uses.len() > 1 {
            for u in &query.pattern_uses {
                if self.repo.find(&with(vec![u.clone()]))?.is_empty() {
                    absent.push(u.clone());
                }
            }
        }
        // Where the probes found none missing alone, it is all of them at once;
        // where there was only one, the pattern that failed was its probe.
        let together = absent.is_empty() && query.pattern_uses.len() > 1;
        if absent.is_empty() {
            absent = query.pattern_uses.clone();
        }
        Ok(Some(Empty::NotInShape { absent, together }))
    }

    /// The three near misses of a shape that matches nothing: the arguments in
    /// the other order, the arguments under another relation, and the shape
    /// with one argument left out.
    fn no_such_shape(&self, shape: &Shape) -> Result<Empty> {
        let hit = |args: Vec<ArgHead>| -> Result<bool> {
            let shape = Shape { concl: shape.concl.clone(), args };
            Ok(!self.repo.find(&Query { shape, limit: 1, ..Query::new() })?.is_empty())
        };
        let mut rev = shape.args.clone();
        rev.reverse();
        let swapped = rev != shape.args && hit(rev)?;
        let named: Vec<usize> =
            (0..shape.args.len()).filter(|i| matches!(shape.args[*i], ArgHead::Named(_))).collect();
        let mut without = Vec::new();
        // Only worth asking of a pattern that named two or more. With one, the
        // answer is always "it matches without it", which says nothing beyond
        // "that constant is never an argument here".
        if named.len() > 1 {
            for &i in &named {
                let mut args = shape.args.clone();
                args[i] = ArgHead::Any;
                if hit(args)?
                    && let ArgHead::Named(n) = &shape.args[i]
                {
                    without.push(n.clone());
                }
            }
        }
        Ok(Empty::NoSuchShape { under: self.under(shape)?, without, swapped })
    }

    /// Which conclusion heads do take these arguments, commonest first. One
    /// search, and only for a pattern that named both a relation and at least
    /// one argument -- without a relation there is nothing to be wrong about.
    fn under(&self, shape: &Shape) -> Result<Vec<(DeclName, usize)>> {
        if shape.concl.is_none() || !shape.args.iter().any(|a| matches!(a, ArgHead::Named(_))) {
            return Ok(Vec::new());
        }
        let free = Shape { concl: None, args: shape.args.clone() };
        let rows = self.repo.find(&Query { shape: free, limit: SPREAD, ..Query::new() })?;
        let mut counts: BTreeMap<DeclName, usize> = BTreeMap::new();
        for d in rows {
            if let Some(c) = d.shape.concl {
                *counts.entry(c).or_default() += 1;
            }
        }
        let mut out: Vec<(DeclName, usize)> = counts.into_iter().collect();
        out.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.as_str().cmp(b.0.as_str())));
        Ok(out)
    }

    /// The modules the query matches once the scope it narrowed to is
    /// dropped, commonest first. One search, and only for a query that
    /// narrowed at all.
    fn elsewhere(&self, query: &Query) -> Result<Vec<(ModuleName, usize)>> {
        if query.module.is_none() && query.source.is_none() {
            return Ok(Vec::new());
        }
        // Wider than `limit`, because what is wanted here is the spread over
        // modules rather than the ten best rows, and narrow enough that a
        // condition matching half the corpus does not pay for a full scan.
        let wider = Query { module: None, source: None, limit: SPREAD, ..query.clone() };
        let rows = self.repo.find(&wider)?;
        let mut counts: BTreeMap<ModuleName, usize> = BTreeMap::new();
        for d in rows {
            *counts.entry(d.module).or_default() += 1;
        }
        let mut out: Vec<(ModuleName, usize)> = counts.into_iter().collect();
        out.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.as_str().cmp(b.0.as_str())));
        Ok(out)
    }
}

/// The sources a query could possibly be answered from, when it says.
///
/// A search that found nothing names no sources, so a staleness warning has to
/// fall back to every one of them -- and after a `lake build` that is a line
/// about the project on the end of every failed Mathlib search, which the
/// project could not have answered either way. `--source` says which source
/// outright; `--in Mathlib.Order` says it by prefix, and the index resolves the
/// prefix for the price of one query. An empty set is "anywhere", which is
/// what the caller already reads it as.
pub fn sources_of(repo: &dyn DeclRepo, query: &Query) -> BTreeSet<SourceId> {
    if let Some(s) = &query.source {
        return BTreeSet::from([s.clone()]);
    }
    let Some(m) = &query.module else { return BTreeSet::new() };
    // Eight, because the roots are disjoint and one row would do; a handful
    // costs the same query and survives a prefix that straddles two of them.
    let probe = Query { module: Some(m.clone()), limit: 8, ..Query::new() };
    repo.find(&probe).map(|r| r.into_iter().map(|d| d.source).collect()).unwrap_or_default()
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
        for scanned in lean_text::scan(&text).decls {
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
