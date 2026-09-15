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

/// Notation to head symbol. Only entries where the mapping is unambiguous: a
/// wrong guess here turns a search into an empty result with no explanation.
const NOTATION: &[(&str, &str)] = &[
    ("≤", "LE.le"),
    ("<", "LT.lt"),
    ("≥", "GE.ge"),
    (">", "GT.gt"),
    ("=", "Eq"),
    ("≠", "Ne"),
    ("↔", "Iff"),
    ("∈", "Membership.mem"),
    ("∉", "Membership.mem"),
    ("⊆", "HasSubset.Subset"),
    ("∣", "Dvd.dvd"),
    ("+", "HAdd.hAdd"),
    ("-", "HSub.hSub"),
    ("*", "HMul.hMul"),
    ("/", "HDiv.hDiv"),
    ("^", "HPow.hPow"),
    ("%", "HMod.hMod"),
    ("∧", "And"),
    ("∨", "Or"),
    ("→", "Arrow"),
    ("∑", "Finset.sum"),
    ("∏", "Finset.prod"),
    ("⊓", "Min.min"),
    ("⊔", "Max.max"),
    ("‖", "Norm.norm"),
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
}

/// Parse a pattern such as `Real.exp _ ≤ _` or `Finset.sum _ _ = _`.
///
/// The rule is small enough to state in full: the pattern is split on the
/// top-level notation symbol, that symbol becomes the conclusion head, and the
/// head identifier of each side becomes an argument. Identifiers elsewhere
/// become `uses` conditions. With no notation symbol, the leading identifier
/// becomes the conclusion head and the rest become arguments.
pub fn parse(pattern: &str) -> Parsed {
    let tokens = tokenize(pattern);
    let vars: Vec<String> =
        dedup_strings(tokens.iter().filter(|t| is_variable(t)).cloned().collect());
    let mut query = Query::new();

    match split_on_operator(&tokens) {
        Some((lhs, op, rhs)) => {
            let concl =
                NOTATION.iter().find(|(sym, _)| *sym == op).map(|(_, head)| DeclName::new(*head));
            let (left_head, left_rest) = side(&lhs);
            let (right_head, right_rest) = side(&rhs);
            query.shape = Shape::new(concl, vec![left_head, right_head]);
            query.uses = dedup(left_rest.into_iter().chain(right_rest).collect());
            Parsed { query, operator: Some(op), extra_constants: Vec::new(), variables: vars }
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
                    query.uses = dedup(rest.to_vec());
                    Parsed { query, operator: None, extra_constants: Vec::new(), variables: vars }
                }
                None => {
                    // Nothing recognisable: fall back to free text rather than
                    // returning an unconstrained query.
                    query.text = Some(pattern.trim().to_string());
                    Parsed { query, operator: None, extra_constants: Vec::new(), variables: vars }
                }
            }
        }
    }
}

fn tokenize(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        if c.is_alphanumeric() || c == '.' || c == '_' || c == '\'' {
            cur.push(c);
        } else {
            if !cur.is_empty() {
                out.push(std::mem::take(&mut cur));
            }
            if !c.is_whitespace() && c != '(' && c != ')' {
                out.push(c.to_string());
            }
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
        .find_map(|t| NOTATION.iter().find(|(sym, _)| sym == t))
        .map(|(_, head)| DeclName::new(*head));
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

    #[test]
    fn underscores_are_wildcards_not_identifiers() {
        let p = parse("_ ≤ Real.exp _");
        assert_eq!(p.query.shape.args, vec![arg("_"), arg("Real.exp")]);
    }
}
