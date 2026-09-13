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
    let mut query = Query::new();

    match split_on_operator(&tokens) {
        Some((lhs, op, rhs)) => {
            let concl =
                NOTATION.iter().find(|(sym, _)| *sym == op).map(|(_, head)| DeclName::new(*head));
            let (left_head, left_rest) = side(&lhs);
            let (right_head, right_rest) = side(&rhs);
            query.shape = Shape::new(concl, vec![left_head, right_head]);
            query.uses = dedup(left_rest.into_iter().chain(right_rest).collect());
            Parsed { query, operator: Some(op), extra_constants: Vec::new() }
        }
        None => {
            let ids = idents(&tokens);
            match ids.split_first() {
                Some((head, rest)) => {
                    let args = tokens
                        .iter()
                        .skip_while(|t| !is_ident(t))
                        .skip(1)
                        .filter(|t| is_ident(t) || *t == "_")
                        .map(|t| ArgHead::parse(t))
                        .collect();
                    query.shape = Shape::new(Some(head.clone()), args);
                    query.uses = dedup(rest.to_vec());
                    Parsed { query, operator: None, extra_constants: Vec::new() }
                }
                None => {
                    // Nothing recognisable: fall back to free text rather than
                    // returning an unconstrained query.
                    query.text = Some(pattern.trim().to_string());
                    Parsed { query, operator: None, extra_constants: Vec::new() }
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
    let notation = tokens
        .iter()
        .find_map(|t| NOTATION.iter().find(|(sym, _)| sym == t))
        .map(|(_, head)| DeclName::new(*head));
    match notation {
        Some(head) => (ArgHead::Named(head), idents(tokens)),
        None => match tokens.iter().find(|t| is_ident(t)) {
            Some(t) => (
                ArgHead::Named(DeclName::new(t.clone())),
                idents(tokens).into_iter().skip(1).collect(),
            ),
            None => (ArgHead::Any, Vec::new()),
        },
    }
}

fn idents(tokens: &[String]) -> Vec<DeclName> {
    tokens.iter().filter(|t| is_ident(t)).map(|t| DeclName::new(t.clone())).collect()
}

fn dedup(mut v: Vec<DeclName>) -> Vec<DeclName> {
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
        // `s`, `f`, `x` are bound variables in the user's head, but the tool
        // cannot know that; they become AND-ed constant conditions.
        assert!(p.query.uses.contains(&DeclName::new("f")));
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
