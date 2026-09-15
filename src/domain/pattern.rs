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

/// Notation to head symbol, with how loosely it binds: the loosest notation on
/// a side is its outermost application, and so is the head symbol the index is
/// keyed by. `a⁻¹ + b⁻¹` is an addition, not an inverse.
///
/// Only entries where the mapping is unambiguous: a wrong guess here turns a
/// search into an empty result with no explanation. `→` is deliberately absent
/// — an implication is a binder in the elaborated term, never a conclusion
/// head, and it is split off before any of this. See [`split_on_arrows`].
const NOTATION: &[(&str, &str, u8)] = &[
    ("≤", "LE.le", 0),
    ("<", "LT.lt", 0),
    ("≥", "GE.ge", 0),
    (">", "GT.gt", 0),
    ("=", "Eq", 0),
    ("≠", "Ne", 0),
    ("↔", "Iff", 0),
    ("∈", "Membership.mem", 0),
    ("∉", "Membership.mem", 0),
    ("⊆", "HasSubset.Subset", 0),
    ("∣", "Dvd.dvd", 0),
    ("∧", "And", 1),
    ("∨", "Or", 1),
    ("∑", "Finset.sum", 2),
    ("∏", "Finset.prod", 2),
    ("+", "HAdd.hAdd", 3),
    ("-", "HSub.hSub", 3),
    ("⊓", "Min.min", 3),
    ("⊔", "Max.max", 3),
    ("*", "HMul.hMul", 4),
    ("/", "HDiv.hDiv", 4),
    ("%", "HMod.hMod", 4),
    ("^", "HPow.hPow", 5),
    ("⁻¹", "Inv.inv", 6),
    ("‖", "Norm.norm", 6),
];

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
    /// How many `→`-separated hypotheses came before the conclusion.
    pub hypotheses: usize,
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
    let all = tokenize(pattern);
    let vars: Vec<String> =
        dedup_strings(all.iter().filter(|t| is_variable(t)).cloned().collect());
    let (hypotheses, tokens) = split_on_arrows(&all);
    let assumed = conditions_of(&hypotheses);
    let count = hypotheses.len();
    let mut query = Query::new();

    match split_on_operator(&tokens) {
        Some((lhs, op, rhs)) => {
            let concl = NOTATION
                .iter()
                .find(|(sym, ..)| *sym == op)
                .map(|(_, head, _)| DeclName::new(*head));
            let (left_head, left_rest) = side(&lhs);
            let (right_head, right_rest) = side(&rhs);
            query.shape = Shape::new(concl, vec![left_head, right_head]);
            query.uses = dedup(left_rest.into_iter().chain(right_rest).chain(assumed).collect());
            Parsed { query, operator: Some(op), extra_constants: Vec::new(), variables: vars, hypotheses: count }
        }
        None => {
            let ids = constants(&tokens);
            match ids.split_first() {
                Some((head, rest)) => {
                    let args = tokens
                        .iter()
                        .skip_while(|t| t.as_str() != head.as_str())
                        .skip(1)
                        .filter(|t| is_ident(t) || *t == "_")
                        .map(|t| arg_head(t))
                        .collect();
                    query.shape = Shape::new(Some(head.clone()), args);
                    query.uses = dedup(rest.iter().cloned().chain(assumed).collect());
                    Parsed { query, operator: None, extra_constants: Vec::new(), variables: vars, hypotheses: count }
                }
                None => {
                    // Nothing recognisable: fall back to free text rather than
                    // returning an unconstrained query.
                    query.text = Some(pattern.trim().to_string());
                    Parsed { query, operator: None, extra_constants: Vec::new(), variables: vars, hypotheses: count }
                }
            }
        }
    }
}

fn tokenize(s: &str) -> Vec<String> {
    /// The superscripts that belong to a postfix operator rather than to the
    /// identifier before it. Rust calls them numeric, so `x⁻¹` would otherwise
    /// tokenize as `x`, `⁻`, and an identifier `¹`.
    const SUPERSCRIPTS: &str = "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿ";
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut cs = s.chars().peekable();
    while let Some(c) = cs.next() {
        if c.is_alphanumeric() || c == '.' || c == '_' || c == '\'' {
            cur.push(c);
            continue;
        }
        if !cur.is_empty() {
            out.push(std::mem::take(&mut cur));
        }
        if c.is_whitespace() || c == '(' || c == ')' {
            continue;
        }
        match c {
            '⁻' => {
                let mut sym = String::from(c);
                while cs.peek().is_some_and(|n| SUPERSCRIPTS.contains(*n)) {
                    sym.push(cs.next().unwrap_or_default());
                }
                out.push(sym);
            }
            // `->` for `→`, because a keyboard has one and not the other, and
            // without this it reads as a subtraction followed by `>`.
            '-' if cs.peek() == Some(&'>') => {
                cs.next();
                out.push("→".to_string());
            }
            _ => out.push(c.to_string()),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn is_ident(t: &str) -> bool {
    t != "_" && t.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_')
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

/// The first notation symbol that names a relation, with the tokens either side.
/// Relations bind loosest, so the first one found is the top level.
fn split_on_operator(tokens: &[String]) -> Option<(Vec<String>, String, Vec<String>)> {
    const RELATIONS: &[&str] = &["≤", "<", "≥", ">", "=", "≠", "↔", "∈", "∉", "⊆", "∣"];
    let i = tokens.iter().position(|t| RELATIONS.contains(&t.as_str()))?;
    Some((tokens[..i].to_vec(), tokens[i].clone(), tokens[i + 1..].to_vec()))
}

/// One side of a relation: its head symbol, and the identifiers left over.
///
/// Notation wins over identifiers, because notation is the outermost
/// application on that side once the relation has been stripped: the head of a
/// norm bracket is `Norm.norm`, and the head of `Real.exp x + y` is `HAdd.hAdd`
/// with `Real.exp` demoted to a `uses` condition.
fn side(tokens: &[String]) -> (ArgHead, Vec<DeclName>) {
    let mut rest = constants(tokens);
    let notation = tokens
        .iter()
        .filter_map(|t| NOTATION.iter().find(|(sym, ..)| sym == t))
        .min_by_key(|(.., prec)| *prec)
        .map(|(_, head, _)| DeclName::new(*head));
    if let Some(head) = notation {
        return (ArgHead::Named(head), rest);
    }
    match tokens.iter().find(|t| is_ident(t)) {
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
    if is_variable(token) { ArgHead::Any } else { ArgHead::parse(token) }
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
        assert!(p.query.text.is_some());
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

    #[test]
    fn underscores_are_wildcards_not_identifiers() {
        let p = parse("_ ≤ Real.exp _");
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("Real.exp")]);
    }
}
