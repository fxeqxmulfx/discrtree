//! `dt find 'Real.exp _ ≤ _'` — turning a written pattern into a [`Query`].
//!
//! This is deliberately a surface parser, not an elaborator. It resolves the
//! notation a user actually types into the head symbols the index is keyed by,
//! and everything it cannot resolve becomes a `--uses` condition rather than a
//! silent failure. Real matching against elaborated skeletons is phase 5; until
//! then the honest description of this is "head symbol plus constants".

use crate::domain::decl::{ArgHead, Shape};
use crate::domain::name::DeclName;
use crate::domain::query::Query;

/// Notation to head symbol, with Lean's own binding strength and whether it
/// associates to the left: the loosest notation on a side is its outermost
/// application, and so is the head symbol the index is keyed by. `a⁻¹ + b⁻¹`
/// is an addition, not an inverse, and `a - b + c` is an addition too, because
/// `+` and `-` bind alike and associate to the left.
///
/// Only entries where the mapping is unambiguous: a wrong guess here turns a
/// search into an empty result with no explanation. `→` is deliberately absent
/// — an implication is a binder in the elaborated term, never a conclusion
/// head, and it is split off before any of this. See [`split_on_arrows`].
const NOTATION: &[(&str, &str, u16, bool)] = &[
    ("↔", "Iff", 20, false),
    ("∨", "Or", 30, false),
    ("∧", "And", 35, false),
    ("≤", "LE.le", 50, false),
    ("<", "LT.lt", 50, false),
    ("≥", "GE.ge", 50, false),
    (">", "GT.gt", 50, false),
    ("=", "Eq", 50, false),
    ("≠", "Ne", 50, false),
    ("∈", "Membership.mem", 50, false),
    // Elaborated as `¬ (a ∈ s)`: see [`parse`], which says so.
    ("∉", "Membership.mem", 50, false),
    ("⊆", "HasSubset.Subset", 50, false),
    ("∣", "Dvd.dvd", 50, false),
    ("<+", "List.Sublist", 50, false),
    ("<+:", "List.IsPrefix", 50, false),
    ("<:+", "List.IsSuffix", 50, false),
    ("<:+:", "List.IsInfix", 50, false),
    ("+", "HAdd.hAdd", 65, true),
    ("-", "HSub.hSub", 65, true),
    ("++", "HAppend.hAppend", 65, true),
    ("∪", "Union.union", 65, true),
    ("::", "List.cons", 67, false),
    ("∑", "Finset.sum", 67, false),
    ("∏", "Finset.prod", 67, false),
    ("⊔", "Max.max", 68, true),
    ("⊓", "Min.min", 69, true),
    ("*", "HMul.hMul", 70, true),
    ("/", "HDiv.hDiv", 70, true),
    ("%", "HMod.hMod", 70, true),
    ("∩", "Inter.inter", 70, true),
    ("\\", "SDiff.sdiff", 70, true),
    ("•", "HSMul.hSMul", 73, false),
    ("^", "HPow.hPow", 75, false),
    ("∘", "Function.comp", 90, false),
    ("⁻¹", "Inv.inv", 1024, false),
];

/// The notation a head symbol is written with, where it has one: `↔` for
/// `Iff`. The first spelling wins, so `Membership.mem` is `∈` and not `∉`.
pub fn symbol(head: &str) -> Option<&'static str> {
    NOTATION.iter().find(|(_, h, ..)| *h == head).map(|(sym, ..)| *sym)
}

/// How loosely a relation binds at most. Notation at this strength or looser
/// is what a statement is *about* -- `a ≤ b ∧ c ≤ d` is a conjunction -- and
/// the pattern is split there; anything tighter is inside one of the sides.
const RELATION: u16 = 50;

/// Symbols written with more than one character, longest first so that `<+:`
/// is not read as `<+` and a stray `:`. Without these `++` tokenized as two
/// additions and `List.take _ _ ++ _ = _` answered with sums.
///
/// The second of each pair is the token it becomes: `->` is `→` and `<=` is
/// `≤`, because a keyboard has one and Lean prints the other.
const COMPOUNDS: &[(&str, &str)] = &[
    ("<:+:", "<:+:"),
    ("<+:", "<+:"),
    ("<:+", "<:+"),
    ("<+", "<+"),
    ("++", "++"),
    ("::", "::"),
    ("->", "→"),
    ("=>", "=>"),
    ("<=", "≤"),
    (">=", "≥"),
    ("!=", "≠"),
];

/// Binders whose variables run up to a comma: `∀ x ∈ s,` and `∑ i ∈ s,`. The
/// `∈` there says where the variable ranges and is not the relation the
/// statement is about, so it is treated as bracketed. See [`depths`].
const BINDER_PREFIXES: &[&str] = &["∀", "∃", "∃!", "∑", "∏", "⋃", "⋂"];

/// Notation that encloses its argument rather than standing between two: an
/// opening delimiter, what closes it, and the constant the pair names.
///
/// A bracket is the outermost application of whatever it encloses, whichever
/// operators are inside it -- `|a + b|` is an absolute value, not an addition
/// -- so these need no binding strength. Parentheses name nothing: they group,
/// and the head is whatever they group.
///
/// `⟫` is matched by prefix, because the field a notation is ascribed with
/// belongs to it: see [`lex`].
const BRACKETS: &[(&str, &str, Option<&str>)] = &[
    ("(", ")", None),
    ("‖", "‖", Some("Norm.norm")),
    ("|", "|", Some("abs")),
    ("⟪", "⟫", Some("Inner.inner")),
];

/// Tokens that are punctuation rather than notation: they carry no head symbol
/// and dropping one loses nothing.
///
/// Binders and their brackets, because [`crate::domain::decl::Shape`] is read
/// off a statement with every binder stripped; coercions and `@`, because they
/// are not what a statement is about. The list exists so that a symbol *not*
/// on it can be reported rather than quietly ignored -- see [`unreadable`].
const IGNORED: &[&str] = &[
    ",", ":", ";", "∀", "∃", "⟨", "⟩", "{", "}", "[", "]", "⦃", "⦄", "↑", "⇑", "@", "✝", "!", "?",
];

/// Lambda syntax. A lambda is a binder, and [`crate::domain::decl::Shape`] is
/// read off a statement with every binder stripped, so there is nothing in the
/// index for the inside of one to be matched against: `fun x => -x` and
/// `fun x => x⁻¹` fill the same argument slot as far as the key is concerned.
///
const BINDERS: &[&str] = &["fun", "λ"];

/// The arrow a lambda's binders end at. Lean writes one after `fun`, and a
/// reader copying a goal back out sometimes writes one without it.
const ARROWS: &[&str] = &["=>", "↦"];

/// What a pattern resolved to, so the caller can tell the user what was
/// understood. An empty search is much easier to debug when the tool says which
/// operator it keyed on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parsed {
    pub query: Query,
    /// The notation that became the conclusion head, if any.
    pub operator: Option<String>,
    /// Identifiers that could not be placed in the shape and became `--uses`.
    pub extra_constants: Vec<DeclName>,
    /// Tokens read as wildcards rather than as constants. See [`is_variable`].
    pub variables: Vec<String>,
    /// Lambdas read as `_`, as they were written. See [`strip_lambdas`].
    ///
    /// Reported rather than applied in silence: the rows that come back answer
    /// a looser question than the one that was asked, and a reader who wrote
    /// `fun _ => -_` is entitled to know that the `-` was not searched for.
    pub lambdas: Vec<String>,
    /// How many `→`-separated hypotheses came before the conclusion.
    pub hypotheses: usize,
    /// Symbols that are neither notation nor punctuation, and so were read as
    /// nothing at all. A pattern with one of these in it says more than the
    /// query says, and the extra rows the query matches are not the rows that
    /// were asked for. Empty when the pattern became a text search: nothing
    /// was dropped there, the whole of it is what is searched for.
    pub unknown: Vec<String>,
}

/// Parse a pattern such as `Real.exp _ ≤ _` or `Finset.sum _ _ = _`.
///
/// The rule is small enough to state in full: the pattern is split on `→`,
/// everything before the last arrow becomes a `--uses` condition, and what is
/// left is split on the top-level notation symbol, that symbol becomes the conclusion head, and the
/// head identifier of each side becomes an argument. Identifiers elsewhere
/// become `uses` conditions. With no notation symbol, the leading identifier
/// becomes the conclusion head and the rest become arguments.
pub fn parse(pattern: &str) -> Parsed {
    let mut p = read(pattern);
    p.query.pattern_uses = p.query.uses.clone();
    p
}

fn read(pattern: &str) -> Parsed {
    let (all, lambdas) = strip_lambdas(&expand_indexing(lex(pattern)));
    let vars: Vec<String> = dedup_strings(all.iter().filter(|t| is_variable(t)).cloned().collect());
    let unknown = unreadable(&all);
    let (hypotheses, tokens) = split_on_arrows(&all);
    let tokens = without_foralls(&tokens);
    let assumed = conditions_of(&hypotheses);
    let count = hypotheses.len();
    let mut query = Query::new();

    match split_on_operator(&tokens) {
        Some((lhs, op, rhs)) => {
            let (left_head, left_rest) = side(&lhs);
            let (right_head, right_rest) = side(&rhs);
            let rest = left_rest.into_iter().chain(right_rest).chain(assumed);
            if op == "∉" {
                // `a ∉ s` is `¬ (a ∈ s)` once elaborated: a negation with one
                // argument, whose sides are a level further down than a shape
                // reaches. What they name is still in the type.
                let sides = [left_head, right_head].into_iter().filter_map(|h| match h {
                    ArgHead::Named(n) => Some(n),
                    ArgHead::Any => None,
                });
                query.shape = Shape::new(
                    Some(DeclName::new("Not")),
                    vec![ArgHead::Named(DeclName::new("Membership.mem"))],
                );
                query.uses = dedup(rest.chain(sides).collect());
            } else {
                let concl = notation(&op).map(|(_, head, ..)| DeclName::new(head));
                query.shape = Shape::new(concl, vec![left_head, right_head]);
                query.uses = dedup(rest.collect());
            }
            Parsed {
                query,
                operator: Some(op),
                extra_constants: Vec::new(),
                variables: vars,
                lambdas,
                hypotheses: count,
                unknown,
            }
        }
        None => {
            let ids = constants(&tokens);
            match ids.split_first() {
                Some((head, rest)) => {
                    let args = tokens
                        .iter()
                        .skip_while(|t| t.as_str() != head.as_str())
                        .skip(1)
                        .filter(|t| is_ident(t) || is_numeral(t) || *t == "_")
                        .map(|t| arg_head(t))
                        .collect();
                    query.shape = Shape::new(Some(head.clone()), args);
                    query.uses = dedup(rest.iter().cloned().chain(assumed).collect());
                    Parsed {
                        query,
                        operator: None,
                        extra_constants: Vec::new(),
                        variables: vars,
                        lambdas,
                        hypotheses: count,
                        unknown,
                    }
                }
                // No name to key on, but notation is a name: `⟪x, y⟫_ℝ`
                // says `Inner.inner` as plainly as `Real.exp x` says
                // `Real.exp`. Which argument is which is another matter --
                // notation hides the implicit ones -- so the head is all this
                // claims, and a head alone still matches.
                None if head_of(&tokens).is_some() => {
                    query.shape = Shape::new(head_of(&tokens), Vec::new());
                    query.uses = dedup(assumed);
                    Parsed {
                        query,
                        operator: None,
                        extra_constants: Vec::new(),
                        variables: vars,
                        lambdas,
                        hypotheses: count,
                        unknown,
                    }
                }
                None => {
                    // Nothing recognisable: fall back to free text rather than
                    // returning an unconstrained query.
                    query.text = pattern.split_whitespace().map(str::to_string).collect();
                    Parsed {
                        query,
                        operator: None,
                        extra_constants: Vec::new(),
                        variables: vars,
                        hypotheses: count,
                        // Nothing was dropped: the pattern is searched whole,
                        // lambda and all.
                        lambdas: Vec::new(),
                        unknown: Vec::new(),
                    }
                }
            }
        }
    }
}

/// Each lambda replaced by the `_` it can honestly be read as, and the lambdas
/// as they were written.
///
/// A lambda runs to the end of the group that encloses it -- that is Lean's
/// own rule, and the reason `(fun x => f x) y` needs its parentheses -- so what
/// is dropped is everything from the binder to the closing bracket, and one
/// argument slot is left where it stood.
///
/// `_` and not nothing: an argument that is a function is still an argument.
/// `Filter.Tendsto (fun _ => -_) Filter.atTop Filter.atBot` asks about the
/// three arguments of `Tendsto`, and the one it cannot key on is the one the
/// index writes `_` for anyway.
fn strip_lambdas(tokens: &[String]) -> (Vec<String>, Vec<String>) {
    let depth = depths(tokens);
    // Where each lambda begins. `fun` and `λ` say so outright; an arrow says
    // so too, one group back, because the binders a lambda ends with are the
    // rest of that group. Without this, `(x => f x)` reads its `=>` as `Eq`
    // applied to `GT.gt` and the pattern comes back a search for equalities.
    let starts: Vec<usize> = (0..tokens.len())
        .filter_map(|k| match tokens[k].as_str() {
            t if BINDERS.contains(&t) => Some(k),
            t if ARROWS.contains(&t) => {
                Some((0..k).rfind(|j| depth[*j] < depth[k]).map_or(0, |j| j + 1))
            }
            _ => None,
        })
        .collect();
    let (mut out, mut found) = (Vec::new(), Vec::new());
    let mut i = 0;
    while i < tokens.len() {
        if !starts.contains(&i) {
            out.push(tokens[i].clone());
            i += 1;
            continue;
        }
        let end = (i..tokens.len()).find(|j| depth[*j] < depth[i]).unwrap_or(tokens.len());
        found.push(tokens[i..end].join(" "));
        out.push("_".to_string());
        i = end;
    }
    (out, found)
}

/// The pattern cut into names and symbols, with a [`SPACE`] wherever it had
/// whitespace.
fn lex(s: &str) -> Vec<String> {
    /// The superscripts that belong to a postfix operator rather than to the
    /// identifier before it. Rust calls them numeric, so `x⁻¹` would otherwise
    /// tokenize as `x`, `⁻`, and an identifier `¹`.
    const SUPERSCRIPTS: &str = "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿ";
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut cs = s.chars().peekable();
    while let Some(c) = cs.next() {
        // A name may have `?` and `!` in it, as in Lean: `List.head?` is one
        // name, and `GetElem?.getElem?` cut at each `?` was `GetElem` and a
        // `.getElem` nothing declares. Only after a name, so that `_` stays a
        // wildcard, and not before `=`, so that `a!=b` is the `≠` it is typed
        // for.
        let in_name = (c == '?' || (c == '!' && cs.peek() != Some(&'='))) && is_ident(&cur);
        if c.is_alphanumeric() || c == '.' || c == '_' || c == '\'' || in_name {
            cur.push(c);
            continue;
        }
        if !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
        if c.is_whitespace() {
            if out.last().is_some_and(|t| t != SPACE) {
                out.push(SPACE.to_string());
            }
            continue;
        }
        let ahead: String = std::iter::once(c).chain(cs.clone().take(3)).collect();
        if let Some((written, token)) = COMPOUNDS.iter().find(|(w, _)| ahead.starts_with(w)) {
            for _ in 1..written.chars().count() {
                cs.next();
            }
            out.push((*token).to_string());
            continue;
        }
        match c {
            // The type a bracket notation is ascribed with -- the `_ℝ` of
            // `⟪x, y⟫_ℝ` -- belongs to the bracket, the way `¹` belongs to
            // `⁻`. Left to itself it tokenizes as an identifier `_ℝ`, which
            // names nothing, and the search became an empty result blaming a
            // condition the user never wrote.
            '⟫' => {
                let mut sym = String::from(c);
                if cs.peek() == Some(&'_') {
                    sym.push(cs.next().unwrap_or_default());
                    while cs.peek().is_some_and(|n| n.is_alphanumeric()) {
                        sym.push(cs.next().unwrap_or_default());
                    }
                }
                out.push(sym);
            }
            '⁻' => {
                let mut sym = String::from(c);
                while cs.peek().is_some_and(|n| SUPERSCRIPTS.contains(*n)) {
                    sym.push(cs.next().unwrap_or_default());
                }
                out.push(sym);
            }
            // What follows the bracket of an index says which index it is --
            // `l[i]?` is another constant from `l[i]` -- and belongs to the
            // bracket the way `¹` belongs to `⁻`. A `!` before `=` is the
            // `!=` Lean reads there.
            ']' => {
                let mut sym = String::from(c);
                let mut ahead = cs.clone();
                match (ahead.next(), ahead.next()) {
                    (Some('?' | '\''), _) => sym.push(cs.next().unwrap_or_default()),
                    (Some('!'), after) if after != Some('=') => {
                        sym.push(cs.next().unwrap_or_default())
                    }
                    _ => {}
                }
                out.push(sym);
            }
            _ => out.push(c.to_string()),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// What whitespace lexes to. It is dropped once the index notation, the one
/// reading that depends on it, is expanded.
const SPACE: &str = " ";

/// How the bracket of an index closes, and the constant the index is then an
/// application of. See [`expand_indexing`].
const INDEXES: &[(&str, &str)] = &[
    ("]", "GetElem.getElem"),
    ("]'", "GetElem.getElem"),
    ("]?", "GetElem?.getElem?"),
    ("]!", "GetElem?.getElem!"),
];

/// Index notation expanded the way Lean's macros expand it: `xs[i]` is
/// `GetElem.getElem xs i`, `xs[i]?` is `GetElem?.getElem? xs i`, `xs[i]!` is
/// `GetElem?.getElem! xs i`, and `xs[i]'h` is the first with its proof written
/// out. Each becomes an application in parentheses, so that it is one term to
/// what is around it and its head is found the way any other head is.
///
/// Read as punctuation, the brackets said nothing: `(_ ++ _)[_]? = _` was an
/// equation with nothing on its left, and the rows were whatever equations
/// ranked first.
///
/// A `[` indexes only a term it is written against, as in Lean: `l[i]` is an
/// index and `f [i]` applies `f` to a list. That is why the lexemes keep their
/// spaces until here.
fn expand_indexing(lexemes: Vec<String>) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    // Each `[` not closed yet: where the term it indexes starts and where the
    // `[` is, or `None` for a list.
    let mut open: Vec<Option<(usize, usize)>> = Vec::new();
    let mut spaced = true;
    for t in lexemes {
        if t == SPACE {
            spaced = true;
            continue;
        }
        if t == "[" {
            open.push(if spaced { None } else { term_start(&out).map(|s| (s, out.len())) });
            out.push(t);
        } else if let Some((_, head)) = INDEXES.iter().find(|(close, _)| *close == t) {
            match open.pop().flatten() {
                Some((start, at)) => {
                    out[at] = "(".to_string();
                    out.push(")".to_string());
                    out.splice(start..start, ["(".to_string(), head.to_string()]);
                    out.push(")".to_string());
                }
                // A list ends at its `]`, and a `?` after one is punctuation.
                None => {
                    out.push("]".to_string());
                    if t != "]" {
                        out.push(t[1..].to_string());
                    }
                }
            }
        } else {
            out.push(t);
        }
        spaced = false;
    }
    out
}

/// Where the term the tokens end with starts, if it is one an index can be
/// written against: a name, a `_`, or a group in parentheses -- which an
/// expanded index is too, so `l[i][j]` indexes `l[i]`.
fn term_start(tokens: &[String]) -> Option<usize> {
    let last = tokens.len().checked_sub(1)?;
    match tokens[last].as_str() {
        ")" => {
            let mut depth = 0;
            (0..=last).rev().find(|j| {
                match tokens[*j].as_str() {
                    ")" => depth += 1,
                    "(" => depth -= 1,
                    _ => {}
                }
                depth == 0
            })
        }
        t if t == "_" || is_ident(t) => Some(last),
        _ => None,
    }
}

fn is_ident(t: &str) -> bool {
    t != "_" && t.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
}

/// A numeric literal, which every elaborated statement spells the same way.
///
/// `0`, `1` and `37` are all `@OfNat.ofNat _ n _` in the term, so a literal
/// anywhere in a pattern is that head symbol and never a name to look up --
/// `Nat.zero_lt_one` is stored as `LT.lt` over two `OfNat.ofNat`s.
fn is_numeral(t: &str) -> bool {
    !t.is_empty() && t.chars().all(|c| c.is_numeric())
}

/// What a numeral is in an elaborated statement.
fn of_nat() -> DeclName {
    DeclName::new("OfNat.ofNat")
}

/// The hypotheses of an implication pattern, and the conclusion left over.
///
/// `→` binds loosest of everything, and what follows the last one is what the
/// statement actually concludes. This matters because it is not how the index
/// is keyed: Lean elaborates `A → B` as a pi type, and [`crate::domain::decl::
/// Shape`] is read off the body with every binder stripped, so a lemma stated
/// with named hypotheses — which is most of Mathlib — has the *conclusion* as
/// its shape and nothing arrow-shaped anywhere. A pattern that kept its arrows
/// could only fail: `HasFDerivAt _ _ _ → HasFDerivAt _ _ _ → HasFDerivAt _ _ _`
/// found nothing while `HasFDerivAt.inner` sat in the index with exactly that
/// statement.
///
/// The hypotheses are not thrown away. They cannot constrain the shape, but
/// what they mention is in the type, so they become `--uses` conditions — see
/// [`conditions_of`].
fn split_on_arrows(tokens: &[String]) -> (Vec<Vec<String>>, Vec<String>) {
    let mut parts: Vec<Vec<String>> = vec![Vec::new()];
    for t in tokens {
        if t == "→" {
            parts.push(Vec::new());
        } else if let Some(last) = parts.last_mut() {
            last.push(t.clone());
        }
    }
    let concl = parts.pop().unwrap_or_default();
    // A pattern that is nothing but arrows, or ends in one, has no conclusion
    // to read; the parts before it are all there is, so nothing is split off.
    if concl.is_empty() {
        return (Vec::new(), tokens.to_vec());
    }
    (parts.into_iter().filter(|p| !p.is_empty()).collect(), concl)
}

/// The conclusion with the `∀ …,` in front of it taken off, because a
/// [`Shape`] is read off a statement with its binders stripped: `∀ {a b : Int},
/// |a + b| ≤ |a| + |b|`, pasted whole out of a goal, asks what `|a + b| ≤ |a| +
/// |b|` asks. `∃` stays: an existential is what such a statement concludes.
fn without_foralls(tokens: &[String]) -> Vec<String> {
    let depth = depths(tokens);
    let mut i = 0;
    while tokens.get(i).is_some_and(|t| t == "∀") {
        match (i + 1..tokens.len()).find(|j| tokens[*j] == "," && depth[*j] == depth[i]) {
            Some(comma) => i = comma + 1,
            None => break,
        }
    }
    tokens[i..].to_vec()
}

/// What the hypotheses can still be searched for: the head symbol of each, and
/// the constants it mentions. Both are in the declaration's type, so both are
/// honest `--uses` conditions — unlike the shape, which only the conclusion has.
fn conditions_of(hypotheses: &[Vec<String>]) -> Vec<DeclName> {
    hypotheses
        .iter()
        .flat_map(|h| {
            let (head, rest) = side(h);
            match head {
                ArgHead::Named(n) => vec![n],
                ArgHead::Any => Vec::new(),
            }
            .into_iter()
            .chain(rest)
        })
        .collect()
}

/// The loosest top-level notation that is a relation or looser, with the
/// tokens either side.
///
/// Loosest and not first: `a = b ↔ c = d` is an `Iff` and `a ≤ b ∧ c ≤ d` is an
/// `And`, and splitting at the first relation read both as something else.
/// Everything this looser than [`RELATION`] associates to the right or not at
/// all, so of equals the first is the outermost.
fn split_on_operator(tokens: &[String]) -> Option<(Vec<String>, String, Vec<String>)> {
    let depth = depths(tokens);
    let (i, _) = tokens
        .iter()
        .zip(&depth)
        .enumerate()
        .filter(|(_, (_, d))| **d == 0)
        .filter_map(|(i, (t, _))| notation(t).map(|(.., prec, _)| (i, prec)))
        .filter(|(_, prec)| *prec <= RELATION)
        .min_by_key(|(_, prec)| *prec)?;
    Some((tokens[..i].to_vec(), tokens[i].clone(), tokens[i + 1..].to_vec()))
}

fn notation(token: &str) -> Option<(&'static str, &'static str, u16, bool)> {
    NOTATION.iter().find(|(sym, ..)| *sym == token).copied()
}

/// One side of a relation: its head symbol, and the identifiers left over.
///
/// Notation wins over identifiers, because notation is the outermost
/// application on that side once the relation has been stripped: the head of a
/// norm bracket is `Norm.norm`, and the head of `Real.exp x + y` is `HAdd.hAdd`
/// with `Real.exp` demoted to a `uses` condition.
fn side(tokens: &[String]) -> (ArgHead, Vec<DeclName>) {
    let mut rest = constants(tokens);
    if let Some(head) = head_of(tokens) {
        return (ArgHead::Named(head), rest);
    }
    match tokens.iter().find(|t| is_ident(t) || is_numeral(t)) {
        Some(t) if is_numeral(t) => (ArgHead::Named(of_nat()), rest),
        // The head of this side is a bound variable, so the side constrains
        // nothing — which is what `_` already means.
        Some(t) if is_variable(t) => (ArgHead::Any, rest),
        Some(t) => {
            if let Some(i) = rest.iter().position(|c| c.as_str() == t.as_str()) {
                rest.remove(i);
            }
            (ArgHead::Named(DeclName::new(t.clone())), rest)
        }
        None => (ArgHead::Any, rest),
    }
}

/// The constant the outermost notation among these tokens stands for.
///
/// A bracket around the whole of them is that outermost application whatever
/// it contains: `|a + b|` is an absolute value and `‖x‖ * ‖y‖` is a product,
/// and reading the first as an addition is not a near miss -- it is five rows
/// about addition, none of which mention an absolute value. Otherwise the
/// loosest infix notation *at the top level* wins; what is inside a bracket
/// belongs to the bracket and is not the head of anything here.
fn head_of(tokens: &[String]) -> Option<DeclName> {
    if let Some((head, inside)) = enclosing(tokens) {
        // Parentheses apply nothing. They group, and the head is what they
        // group: `(Real.exp x) ≤ y` asks what `Real.exp x ≤ y` asks.
        return match head {
            Some(h) => Some(DeclName::new(h)),
            None => head_of(inside),
        };
    }
    let depth = depths(tokens);
    let top: Vec<_> = tokens
        .iter()
        .zip(&depth)
        .filter(|(_, d)| **d == 0)
        .filter_map(|(t, _)| notation(t))
        .collect();
    let loosest = top.iter().map(|(.., prec, _)| *prec).min()?;
    let mut at = top.into_iter().filter(|(.., prec, _)| *prec == loosest);
    // `a - b + c` is `(a - b) + c`: of operators that associate to the left,
    // the last one is applied outermost.
    let first = at.next()?;
    let outer = if first.3 { at.next_back().unwrap_or(first) } else { first };
    Some(DeclName::new(outer.1))
}

/// How deeply each token is bracketed. An opening delimiter and its closer are
/// both reported at the depth outside the group they make, so that the tokens
/// at depth 0 are exactly the ones the side is an application of.
///
/// `‖` and `|` close what they open, so a run of them alternates; `⟪` and `(`
/// have closers of their own. An unclosed bracket leaves everything after it
/// deeper, which is what a reader who typed one means anyway.
fn depths(tokens: &[String]) -> Vec<usize> {
    let mut out = Vec::with_capacity(tokens.len());
    let mut open: Vec<&str> = Vec::new();
    for t in tokens {
        if open.last().is_some_and(|close| t.starts_with(close)) {
            open.pop();
            out.push(open.len());
        } else if BINDER_PREFIXES.contains(&t.as_str()) {
            out.push(open.len());
            open.push(",");
        } else if let Some((_, close, _)) = BRACKETS.iter().find(|(o, ..)| *o == t.as_str()) {
            out.push(open.len());
            open.push(close);
        } else {
            out.push(open.len());
        }
    }
    out
}

/// The bracket that encloses every one of these tokens, if one does: the
/// constant it names, and what is inside it.
fn enclosing(tokens: &[String]) -> Option<(Option<&'static str>, &[String])> {
    let (first, rest) = tokens.split_first()?;
    let (_, close, head) = BRACKETS.iter().find(|(o, ..)| *o == first.as_str())?;
    let (last, inside) = rest.split_last()?;
    if !last.starts_with(close) {
        return None;
    }
    // `|a| + |b|` opens and closes before the end: the group the first token
    // makes is not the whole side, and the `+` between them is the head.
    depths(tokens)[1..tokens.len() - 1].iter().all(|d| *d > 0).then_some((*head, inside))
}

/// Symbols the parser reads as nothing: neither notation, nor a bracket, nor
/// punctuation.
///
/// Dropping one silently is the worst answer available. The pattern still
/// matches -- more loosely, having lost the one thing that distinguished it --
/// so the rows come back looking like an answer, and `|_ + _| ≤ |_| + |_|`
/// returned five lemmas about addition with no absolute value in them. An
/// empty result says which condition to blame; those rows say nothing.
fn unreadable(tokens: &[String]) -> Vec<String> {
    let known = |t: &String| {
        t == "_"
            || is_ident(t)
            || is_numeral(t)
            || t == "→"
            || IGNORED.contains(&t.as_str())
            || notation(t).is_some()
            || BRACKETS.iter().any(|(o, c, _)| *o == t.as_str() || t.starts_with(c))
    };
    dedup_strings(tokens.iter().filter(|t| !known(t)).cloned().collect())
}

/// Whether a token names a bound variable rather than something to look up.
///
/// One letter, plus the decorations Lean's own printer adds: `a`, `x'`, `f₁`,
/// `α`. That is how every binder in a Mathlib statement is spelled and how no
/// global constant is — a declaration worth searching for has a namespace, or
/// at least a word. Reading them as constants is what made
/// `a ≤ b → b⁻¹ ≤ a⁻¹` answer `no match: --uses a, --uses b`: three AND-ed
/// conditions on names nothing declares, from a pattern that named none.
///
/// Syntactic on purpose. Asking the index whether `a` resolves would make the
/// same pattern mean different things in different projects, and the one
/// project where something is called `a` is the one where that is a typo.
fn is_variable(t: &str) -> bool {
    let mut cs = t.chars();
    cs.next().is_some_and(char::is_alphabetic) && cs.all(|c| c.is_numeric() || "'_!?".contains(c))
}

/// The identifiers that name a declaration, which is every identifier that is
/// not a bound variable.
fn constants(tokens: &[String]) -> Vec<DeclName> {
    tokens
        .iter()
        .filter(|t| is_ident(t) && !is_variable(t))
        .map(|t| DeclName::new(t.clone()))
        .collect()
}

/// One argument of a prefix pattern. A variable is a wildcard, not a name.
fn arg_head(token: &str) -> ArgHead {
    match token {
        t if is_numeral(t) => ArgHead::Named(of_nat()),
        t if is_variable(t) => ArgHead::Any,
        t => ArgHead::parse(t),
    }
}

fn dedup(mut v: Vec<DeclName>) -> Vec<DeclName> {
    v.sort();
    v.dedup();
    v
}

fn dedup_strings(mut v: Vec<String>) -> Vec<String> {
    v.sort();
    v.dedup();
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    fn arg(s: &str) -> ArgHead {
        ArgHead::parse(s)
    }

    #[test]
    fn an_infix_relation_becomes_the_conclusion_head() {
        let p = parse("Real.exp _ ≤ _");
        assert_eq!(p.operator.as_deref(), Some("≤"));
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("Real.exp"), arg("_")]);
    }

    #[test]
    fn both_sides_contribute_their_head() {
        let p = parse("Finset.sum s f = Real.exp x");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")));
        assert_eq!(p.query.shape.args, vec![arg("Finset.sum"), arg("Real.exp")]);
        // `s`, `f` and `x` are binders. Nothing declares them, so searching for
        // them can only subtract matches.
        assert!(p.query.uses.is_empty(), "{:?}", p.query.uses);
        assert_eq!(p.variables, vec!["f", "s", "x"]);
    }

    /// The pattern from the report: every identifier in it is a binder, and
    /// reading them as constants made the answer `no match` with four
    /// conditions to blame, none of which the user had written.
    #[test]
    fn a_pattern_of_nothing_but_binders_constrains_only_its_shape() {
        let p = parse("a ≤ b");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("_")]);
        assert!(p.query.uses.is_empty());
    }

    /// The pattern from the report. `fun` is a word, so it was read as a
    /// constant, resolved to `Lean.Compiler.LCNF.Code.fun` -- the only thing
    /// in the index whose name ends that way -- and the search died there.
    #[test]
    fn a_lambda_is_the_argument_slot_it_fills_and_nothing_more() {
        let p = parse("Filter.Tendsto (fun _ => -_) Filter.atTop Filter.atBot");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Filter.Tendsto")));
        assert_eq!(
            p.query.shape.args,
            vec![arg("_"), arg("Filter.atTop"), arg("Filter.atBot")],
            "one slot, and it is a wildcard"
        );
        assert!(!p.query.uses.iter().any(|u| u.as_str() == "fun"), "{:?}", p.query.uses);
        assert_eq!(p.lambdas.len(), 1, "and the reader is told what was dropped");
    }

    #[test]
    fn a_lambda_ends_where_its_brackets_do() {
        // The binder swallows the rest of its group and no more: `Finset.sum`
        // keeps both arguments, and the `= _` outside is still the relation.
        let p = parse("Finset.sum _ (fun i => Real.exp i) = _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")));
        assert_eq!(p.query.shape.args, vec![arg("Finset.sum"), arg("_")]);
        // What is inside the lambda is inside the lambda. `Real.exp` is not in
        // the conclusion's shape, and claiming it as a `--uses` would be
        // claiming the statement mentions it at this depth.
        assert!(p.query.uses.is_empty(), "{:?}", p.query.uses);
    }

    /// An arrow is a binder even with the keyword left off, and reading it as
    /// two notations is the misreading that costs most: `=` binds loosest, so
    /// `x => f x` became an equation and the pattern came back a search for
    /// equalities.
    #[test]
    fn an_arrow_with_no_keyword_before_it_is_still_a_lambda() {
        let p = parse("Filter.Tendsto (x => -x) Filter.atTop Filter.atBot");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Filter.Tendsto")));
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("Filter.atTop"), arg("Filter.atBot")]);
        assert_eq!(p.operator, None, "no relation was written");
    }

    #[test]
    fn a_pattern_with_no_lambda_in_it_reports_none() {
        assert!(parse("Real.exp _ ≤ _").lambdas.is_empty());
        // `->` is an implication and not an arrow of this kind.
        assert!(parse("a ≤ b -> b⁻¹ ≤ a⁻¹").lambdas.is_empty());
    }

    /// A binder is one letter and its decorations. Anything with a word in it
    /// is a name, and a name is looked up even when it is short.
    #[test]
    fn a_short_name_is_still_a_name() {
        assert!(is_variable("a"));
        assert!(is_variable("x'"));
        assert!(is_variable("f₁"));
        assert!(is_variable("α"));
        assert!(is_variable("n_1"));
        assert!(!is_variable("id"));
        assert!(!is_variable("Ne"));
        assert!(!is_variable("Nat.succ"));
        assert!(!is_variable("_"));
    }

    /// A prefix pattern takes its head from the first identifier that names
    /// something; the binders after it are arguments, and arguments that are
    /// binders are wildcards.
    #[test]
    fn a_prefix_pattern_skips_binders_for_its_head() {
        let p = parse("Continuous f");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Continuous")));
        assert_eq!(p.query.shape.args, vec![arg("_")]);
        assert!(p.query.uses.is_empty());
    }

    #[test]
    fn notation_on_a_side_resolves_too() {
        let p = parse("‖x‖ ≤ _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args[0], arg("Norm.norm"));
    }

    #[test]
    fn a_prefix_pattern_uses_its_leading_identifier() {
        let p = parse("Continuous Real.exp");
        assert_eq!(p.operator, None);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Continuous")));
        assert_eq!(p.query.shape.args, vec![arg("Real.exp")]);
    }

    #[test]
    fn parentheses_do_not_change_the_reading() {
        assert_eq!(parse("(Real.exp x) ≤ y").query, parse("Real.exp x ≤ y").query);
    }

    #[test]
    fn an_unparseable_pattern_falls_back_to_text_not_to_everything() {
        let p = parse("!!!");
        assert!(!p.query.text.is_empty());
        assert!(!p.query.is_empty(), "the fallback must still constrain the search");
    }

    /// The report: `HasFDerivAt.inner` takes two hypotheses and concludes a
    /// third `HasFDerivAt`, and a pattern written that way found nothing,
    /// because the shape in the index is the conclusion alone.
    #[test]
    fn an_implication_is_searched_for_by_its_conclusion() {
        let p = parse("HasFDerivAt _ _ _ → HasFDerivAt _ _ _ → HasFDerivAt _ _ _");
        assert_eq!(p.hypotheses, 2);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("HasFDerivAt")));
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("_"), arg("_")]);
        // The hypotheses are in the type even though they are not in the
        // shape, so they are still worth a condition.
        assert_eq!(p.query.uses, vec![DeclName::new("HasFDerivAt")]);
    }

    #[test]
    fn a_hypothesis_contributes_what_it_mentions() {
        let p = parse("Real.exp x ≤ y → x ≤ Real.log y");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("Real.log")]);
        assert!(p.query.uses.contains(&DeclName::new("Real.exp")));
        assert!(p.query.uses.contains(&DeclName::new("LE.le")));
    }

    /// The other half of the report's first pattern. Without the postfix
    /// operator both sides are binders, and the shape says nothing at all.
    #[test]
    fn an_inverse_is_a_head_symbol() {
        let p = parse("a ≤ b → b⁻¹ ≤ a⁻¹");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("Inv.inv"), arg("Inv.inv")]);
        assert_eq!(p.query.uses, vec![DeclName::new("LE.le")]);
    }

    /// Notation binds at different strengths, and the head symbol of a side is
    /// its outermost application — the loosest operator on it.
    #[test]
    fn the_loosest_notation_on_a_side_is_its_head() {
        assert_eq!(parse("a⁻¹ + b⁻¹ ≤ _").query.shape.args[0], arg("HAdd.hAdd"));
        assert_eq!(parse("‖x‖ * ‖y‖ = _").query.shape.args[0], arg("HMul.hMul"));
    }

    #[test]
    fn an_ascii_arrow_is_an_arrow_not_a_subtraction() {
        assert_eq!(parse("a ≤ b -> c ≤ d").query, parse("a ≤ b → c ≤ d").query);
    }

    /// A pattern that ends in an arrow has no conclusion to read. It must not
    /// lose the part that was written, and must not panic.
    #[test]
    fn a_pattern_with_nothing_after_the_arrow_keeps_what_there_is() {
        let p = parse("Real.exp _ ≤ _ →");
        assert_eq!(p.hypotheses, 0);
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert!(!parse("→").query.is_empty());
    }

    /// The report: the inner product written the way Lean prints it. The
    /// bracket is the head symbol, and the `_ℝ` that says which field is not
    /// a constant to look up -- read as one it was the only thing the error
    /// message could name.
    #[test]
    fn a_bracket_notation_is_a_head_symbol_and_its_ascription_is_not_a_name() {
        let p = parse("⟪_, _⟫_ℝ = _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")));
        assert_eq!(p.query.shape.args, vec![arg("Inner.inner"), arg("_")]);
        assert!(p.query.uses.is_empty(), "{:?}", p.query.uses);
        // The bracket carries its own head whichever field is named, and
        // naming none is how the `RCLike` notation is spelled.
        assert_eq!(parse("⟪x, y⟫_𝕜 = _").query, p.query);
        assert_eq!(parse("⟪x, y⟫ = _").query, p.query);
    }

    /// A pattern that is nothing but notation still says what it concludes.
    /// Which argument is which is hidden by the notation, so the head is all
    /// that is claimed -- but a head alone is a search, and free text is not.
    #[test]
    fn notation_alone_is_a_shape_not_a_text_search() {
        let p = parse("⟪x, y⟫_ℝ");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Inner.inner")));
        assert!(p.query.shape.args.is_empty());
        assert!(p.query.text.is_empty());
        assert_eq!(parse("‖x‖").query.shape.concl, Some(DeclName::new("Norm.norm")));
    }

    /// The report: `abs_add_le` is `|a + b| ≤ |a| + |b|`, and the pattern
    /// written that way returned five lemmas about addition with no absolute
    /// value in them. The bracket was dropped because the `+` inside it binds
    /// looser, and looser is how the head of a side is chosen -- but a bracket
    /// is not on the side, it *is* the side.
    #[test]
    fn a_bracket_is_the_head_of_everything_it_encloses() {
        let p = parse("|_ + _| ≤ |_| + |_|");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("abs"), arg("HAdd.hAdd")]);
        // The same defect, one bracket over: `‖_ + _‖ ≤ _` matched anything
        // with an addition on the left.
        assert_eq!(parse("‖_ + _‖ ≤ _").query.shape.args[0], arg("Norm.norm"));
        // And the reading that was already right stays right: two brackets
        // with an operator between them are that operator.
        assert_eq!(parse("|_| + |_| ≤ _").query.shape.args[0], arg("HAdd.hAdd"));
    }

    /// A relation inside a bracket is not the one the statement is about.
    #[test]
    fn a_bracketed_relation_does_not_split_the_pattern() {
        let p = parse("‖f x - f y‖ ≤ _");
        assert_eq!(p.operator.as_deref(), Some("≤"));
        assert_eq!(p.query.shape.args[0], arg("Norm.norm"));
    }

    /// A symbol that means something to Lean and nothing to this parser used
    /// to be read as nothing, which quietly widened the search. It is now
    /// reported, so the caller can say `no match` and name it.
    #[test]
    fn a_symbol_the_parser_cannot_read_is_reported_rather_than_dropped() {
        assert_eq!(parse("_ ∆ _ ⊆ _").unknown, vec!["∆"]);
        // Notation, brackets and punctuation are read, not reported -- a
        // statement pasted whole out of a goal is mostly punctuation.
        assert!(parse("∀ {a b : Int}, |a + b| ≤ |a| + |b|").unknown.is_empty());
        assert!(parse("Real.exp _ ≤ _ → ⟪_, _⟫_ℝ = _").unknown.is_empty());
        // Nothing was dropped from a pattern that became a text search: the
        // whole of it is what is searched for.
        assert!(!parse("∫ x, f x").query.text.is_empty());
        assert!(parse("∫ x, f x").unknown.is_empty());
    }

    /// A literal is not a name and not a symbol to complain about: every
    /// elaborated statement spells `0`, `1` and `37` as `OfNat.ofNat`, so a
    /// pattern with one in it can say exactly that.
    #[test]
    fn a_numeral_is_the_head_symbol_a_literal_elaborates_to() {
        let p = parse("0 < 1");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LT.lt")));
        assert_eq!(p.query.shape.args, vec![arg("OfNat.ofNat"), arg("OfNat.ofNat")]);
        assert!(p.query.uses.is_empty(), "a literal is nothing to search for: {:?}", p.query.uses);
        assert!(p.unknown.is_empty(), "{:?}", p.unknown);
        // Inside a side it is an argument like any other, and the side's own
        // head still wins.
        assert_eq!(parse("_ + 1 ≤ Real.exp _").query.shape.args[0], arg("HAdd.hAdd"));
        assert_eq!(parse("Nat.succ 1").query.shape.args, vec![arg("OfNat.ofNat")]);
    }

    /// The report: `List.take _ _ ++ _ = _` answered with sums, because `++`
    /// was read as two `+`. A symbol spelled with several characters is one
    /// token, and the longest spelling wins.
    #[test]
    fn a_symbol_of_several_characters_is_one_symbol() {
        let p = parse("List.take _ _ ++ _ = _");
        assert_eq!(p.query.shape.args, vec![arg("HAppend.hAppend"), arg("_")]);
        assert!(p.unknown.is_empty(), "{:?}", p.unknown);
        let p = parse("l <+ a :: l'");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("List.Sublist")));
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("List.cons")]);
        assert_eq!(parse("_ <+: _").query.shape.concl, Some(DeclName::new("List.IsPrefix")));
        assert_eq!(parse("_ <:+: _").query.shape.concl, Some(DeclName::new("List.IsInfix")));
        assert_eq!(parse("_ <= _").query, parse("_ ≤ _").query);
    }

    /// `a = b ↔ c = d` is an `Iff` of two equations. Splitting at the first
    /// relation made it an equation whose right side was an `Iff`.
    #[test]
    fn the_loosest_relation_is_the_one_the_statement_is_about() {
        let p = parse("_ = _ ↔ _ = _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Iff")));
        assert_eq!(p.query.shape.args, vec![arg("Eq"), arg("Eq")]);
        let p = parse("a ≤ b ∧ c ≤ d");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("And")));
        assert_eq!(p.query.shape.args, vec![arg("LE.le"), arg("LE.le")]);
        let p = parse("a ∈ l ↔ a = b ∨ a ∈ l'");
        assert_eq!(p.query.shape.args, vec![arg("Membership.mem"), arg("Or")]);
    }

    /// `a - b + c` is `(a - b) + c`, and `a ^ b ^ c` is `a ^ (b ^ c)`.
    #[test]
    fn operators_that_bind_alike_associate_as_lean_says() {
        assert_eq!(parse("a - b + c = _").query.shape.args[0], arg("HAdd.hAdd"));
        assert_eq!(parse("a * b ^ c = _").query.shape.args[0], arg("HMul.hMul"));
        assert_eq!(parse("a :: l ++ m = _").query.shape.args[0], arg("HAppend.hAppend"));
    }

    /// The variable of a big operator or a quantifier ranges over something,
    /// and that `∈` is not the relation the statement is about.
    #[test]
    fn a_binder_range_is_not_a_relation() {
        let p = parse("∑ i ∈ s, f i = _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Eq")));
        assert_eq!(p.query.shape.args, vec![arg("Finset.sum"), arg("_")]);
        let p = parse("∀ {a b : Int}, |a + b| ≤ |a| + |b|");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("LE.le")));
        assert_eq!(p.query.shape.args, vec![arg("abs"), arg("HAdd.hAdd")]);
    }

    /// `a ∉ s` elaborates to `¬ (a ∈ s)`, and that is what the index keys it by.
    #[test]
    fn not_in_is_a_negated_membership() {
        let p = parse("_ ∉ Finset.range _");
        assert_eq!(p.query.shape.concl, Some(DeclName::new("Not")));
        assert_eq!(p.query.shape.args, vec![arg("Membership.mem")]);
        assert_eq!(p.query.uses, vec![DeclName::new("Finset.range")]);
    }

    /// The report: `(_ ++ _)[_]? = _` was read as `_ = _`, because the
    /// brackets and the `?` were punctuation, and the rows were whatever
    /// equations ranked first. An index is the constant Lean expands it to.
    #[test]
    fn an_index_is_the_constant_its_notation_expands_to() {
        let p = parse("(_ ++ _)[_]? = _");
        assert_eq!(p.query.shape.args, vec![arg("GetElem?.getElem?"), arg("_")]);
        assert!(p.unknown.is_empty(), "{:?}", p.unknown);
        // The lemma asked for is in the index as `Option`, `getElem?`,
        // `getElem?`; the first row that came back was `↑1 = 1`.
        let stored = |args: &[&str]| {
            Shape::new(Some(DeclName::new("Eq")), args.iter().map(|a| arg(a)).collect())
        };
        assert!(p.query.shape.matches(&stored(&[
            "Option",
            "GetElem?.getElem?",
            "GetElem?.getElem?"
        ])));
        assert!(!p.query.shape.matches(&stored(&["ENat", "Nat.cast", "OfNat.ofNat"])));
        assert_eq!(parse("_[_]? = _").query, p.query);
        for (pattern, head) in [
            ("l[i] = _", "GetElem.getElem"),
            ("xs[i]'h = _", "GetElem.getElem"),
            ("l[i]! = _", "GetElem?.getElem!"),
            ("l[i][j]? = _", "GetElem?.getElem?"),
            ("(l ++ m)[i + 1] = _", "GetElem.getElem"),
        ] {
            assert_eq!(parse(pattern).query.shape.args[0], arg(head), "{pattern}");
        }
        // An index binds tighter than an operator, and than an application.
        assert_eq!(parse("l[i] + 1 = _").query.shape.args[0], arg("HAdd.hAdd"));
        let p = parse("Nat.succ l[i] = _");
        assert_eq!(p.query.shape.args[0], arg("Nat.succ"));
        assert_eq!(p.query.uses, vec![DeclName::new("GetElem.getElem")]);
        // A bracket with a space before it is a list, as in Lean.
        let p = parse("List.sum [a] = _");
        assert_eq!(p.query.shape.args[0], arg("List.sum"));
        assert!(p.query.uses.is_empty(), "{:?}", p.query.uses);
    }

    /// The constant an index stands for could not be written instead: cut at
    /// each `?`, `GetElem?.getElem?` was `GetElem` and a `.getElem` that reads
    /// as nothing.
    #[test]
    fn a_name_may_have_a_question_mark_or_a_bang_in_it() {
        let p = parse("GetElem?.getElem? (_ ++ _) _ = _");
        assert_eq!(p.query.shape.args, vec![arg("GetElem?.getElem?"), arg("_")]);
        assert!(p.unknown.is_empty(), "{:?}", p.unknown);
        assert_eq!(parse("List.head? _ = _").query.shape.args[0], arg("List.head?"));
        assert_eq!(parse("Option.get! _ = _").query.shape.args[0], arg("Option.get!"));
        // `!=` is still the `≠` it is typed for, after a name or a bracket.
        assert_eq!(parse("a!=b").query, parse("a ≠ b").query);
        assert_eq!(parse("l[i]!=x").query, parse("l[i] ≠ x").query);
    }

    #[test]
    fn underscores_are_wildcards_not_identifiers() {
        let p = parse("_ ≤ Real.exp _");
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("Real.exp")]);
    }
}
