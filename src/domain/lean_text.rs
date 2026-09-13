//! Reading Lean as text, for corpora that are indexed but never built.
//!
//! This is not a parser for Lean and does not pretend to be one. It is a parse
//! against a known shape: a declaration header at column zero, a statement
//! running to the `:=` or `where` that ends it. Rows it produces carry
//! `elaborated: false`, and nothing downstream may treat them as if they had
//! been through the elaborator.

use crate::domain::name::{DeclName, ModuleName};

/// One declaration as it appears in a file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scanned {
    pub name: DeclName,
    pub kind: String,
    /// The statement, from after the name to the start of the proof.
    pub statement: String,
    /// Docstring immediately above the declaration, if any.
    pub doc: Option<String>,
    /// Dotted identifiers occurring in the declaration. The only approximation
    /// of dependencies available without an elaborator; the caller intersects
    /// them with known names to drop bound variables.
    pub idents: Vec<DeclName>,
    pub has_sorry: bool,
    /// 1-based, inclusive.
    pub line_start: u32,
    pub line_end: u32,
}

const HEADERS: &[&str] = &[
    "theorem ",
    "lemma ",
    "def ",
    "abbrev ",
    "instance ",
    "structure ",
    "class ",
    "inductive ",
    "axiom ",
    "opaque ",
];

/// Modifiers that may precede a declaration header on the same line, in any
/// order and any number. An attribute block is handled separately, since
/// `@[simp, norm_cast]` and `@[to_additive existing]` cannot be enumerated.
const MODIFIERS: &[&str] = &[
    "private ",
    "protected ",
    "noncomputable ",
    "partial ",
    "unsafe ",
    "nonrec ",
    "scoped ",
    "local ",
];

/// The modules a file imports. For a text corpus these are the only structural
/// dependency information there is.
pub fn imports(text: &str) -> Vec<ModuleName> {
    text.lines()
        .take_while(|l| {
            let t = l.trim_start();
            t.is_empty() || t.starts_with("import ") || t.starts_with("--") || t.starts_with("/-")
        })
        .filter_map(|l| l.trim().strip_prefix("import "))
        .map(|m| ModuleName::new(m.trim()))
        .collect()
}

/// What a file turned out to contain.
pub struct Scan {
    pub decls: Vec<Scanned>,
    /// Declarations with no name of their own: `instance : Foo Bar := ...`.
    ///
    /// Lean generates a name for these; nothing in the source says what it is,
    /// so there is no honest key to index them under. They are counted rather
    /// than dropped in silence, because 516 of FLT's 3743 declarations are of
    /// this kind and a corpus that quietly omits a seventh of itself is a
    /// corpus that lies about what it does not contain.
    pub anonymous: usize,
}

/// Every declaration in a file.
pub fn scan(text: &str) -> Scan {
    let lines: Vec<&str> = text.lines().collect();
    let mut anonymous = 0usize;
    let mut out: Vec<Scanned> = Vec::new();
    let mut namespaces: Vec<String> = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i];
        if let Some(rest) = line.strip_prefix("namespace ") {
            namespaces.push(rest.trim().to_string());
        } else if let Some(ended) = line.strip_prefix("end ") {
            let ended = ended.trim();
            if namespaces.last().map(String::as_str) == Some(ended) {
                namespaces.pop();
            }
        } else if let Some((kind, after)) = header(line) {
            let start = i;
            let end = declaration_end(&lines, i);
            let body = lines[start..=end].join("\n");
            let base = first_token(after);
            let name = qualify(&namespaces, base);
            if base.is_empty() {
                anonymous += 1;
            }
            if !base.is_empty() && !name.is_internal() {
                out.push(Scanned {
                    name,
                    kind: kind.to_string(),
                    statement: statement_of(&body, after),
                    doc: docstring_above(&lines, start),
                    idents: dotted_identifiers(&body),
                    has_sorry: mentions_sorry(&body),
                    line_start: start as u32 + 1,
                    line_end: end as u32 + 1,
                });
            }
            i = end;
        }
        i += 1;
    }
    Scan { decls: out, anonymous }
}

/// A declaration header at column zero, returning its kind and what follows.
/// Column zero is what makes this reliable: a `have` or a nested `def` inside a
/// proof is always indented.
fn header(line: &str) -> Option<(&'static str, &str)> {
    let mut rest = line;
    loop {
        if let Some(h) = HEADERS.iter().find(|h| rest.starts_with(**h)) {
            return Some((h.trim_end(), &rest[h.len()..]));
        }
        if let Some(after) = attribute(rest) {
            rest = after;
            continue;
        }
        let m = MODIFIERS.iter().find(|m| rest.starts_with(**m))?;
        rest = &rest[m.len()..];
    }
}

/// What follows an inline `@[...]` attribute block, if the line opens with one.
/// Brackets nest: `@[to_additive (attr := simp)]` is one block.
fn attribute(line: &str) -> Option<&str> {
    let rest = line.strip_prefix("@[")?;
    let mut depth = 1usize;
    for (i, c) in rest.char_indices() {
        match c {
            '[' => depth += 1,
            ']' => {
                depth -= 1;
                if depth == 0 {
                    return Some(rest[i + 1..].trim_start());
                }
            }
            _ => {}
        }
    }
    None
}

/// A declaration runs until the next line at column zero that starts something
/// else, or the end of the file.
fn declaration_end(lines: &[&str], start: usize) -> usize {
    let mut end = start;
    for (i, line) in lines.iter().enumerate().skip(start + 1) {
        let starts_something = !line.is_empty()
            && !line.starts_with(char::is_whitespace)
            && (header(line).is_some()
                || line.starts_with("namespace ")
                || line.starts_with("end ")
                || line.starts_with("section")
                || line.starts_with("open ")
                || line.starts_with("variable")
                || line.starts_with("/--")
                || line.starts_with("@["));
        if starts_something {
            break;
        }
        if !line.trim().is_empty() {
            end = i;
        }
    }
    end
}

/// Everything between the declaration's name and the start of its proof.
fn statement_of(body: &str, after_name: &str) -> String {
    let name_len = first_token(after_name).len();
    let from_name = match body.find(after_name) {
        Some(p) => &body[p + name_len..],
        None => body,
    };
    // FLT delegates every proof to `p2m_exact_reverting`; Mathlib-style sources
    // use `:= by`. Either way the statement ends at the first top-level `:=`.
    let cut = [":= by", ":=\n", ":= ", "\n  where", ":= fun"]
        .iter()
        .filter_map(|m| from_name.find(m))
        .min()
        .unwrap_or(from_name.len());
    from_name[..cut].trim().to_string()
}

fn first_token(s: &str) -> &str {
    s.trim_start().split(|c: char| c.is_whitespace() || "({[:".contains(c)).next().unwrap_or("")
}

fn qualify(namespaces: &[String], name: &str) -> DeclName {
    if namespaces.is_empty() || name.starts_with("_root_.") {
        DeclName::new(name.trim_start_matches("_root_."))
    } else {
        DeclName::new(format!("{}.{}", namespaces.join("."), name))
    }
}

/// A `/-- ... -/` docstring directly above the declaration.
fn docstring_above(lines: &[&str], start: usize) -> Option<String> {
    let mut i = start;
    // Attributes sit between the docstring and the declaration.
    while i > 0 && lines[i - 1].starts_with("@[") {
        i -= 1;
    }
    if i == 0 || !lines[i - 1].trim_end().ends_with("-/") {
        return None;
    }
    let open = (0..i).rev().find(|j| lines[*j].trim_start().starts_with("/--"))?;
    let text = lines[open..i].join("\n");
    Some(text.trim().trim_start_matches("/--").trim_end_matches("-/").trim().to_string())
}

/// Dotted capitalised identifiers: the only dependency signal in text. Bare
/// lowercase tokens are dropped because they are overwhelmingly bound
/// variables, and a dependency list full of `x` and `hf` is worse than none.
fn dotted_identifiers(body: &str) -> Vec<DeclName> {
    let mut out: Vec<DeclName> = Vec::new();
    let mut cur = String::new();
    let push = |cur: &mut String, out: &mut Vec<DeclName>| {
        let t = std::mem::take(cur);
        let looks_qualified = t.contains('.') && !t.starts_with('.') && !t.ends_with('.');
        let looks_global = t.chars().next().is_some_and(char::is_uppercase);
        if (looks_qualified || looks_global) && !t.chars().all(|c| c.is_numeric() || c == '.') {
            let n = DeclName::new(t);
            if !n.is_internal() && !out.contains(&n) {
                out.push(n);
            }
        }
    };
    for c in body.chars() {
        if c.is_alphanumeric() || c == '.' || c == '_' || c == '\'' {
            cur.push(c);
        } else if !cur.is_empty() {
            push(&mut cur, &mut out);
        }
    }
    if !cur.is_empty() {
        push(&mut cur, &mut out);
    }
    out.sort();
    out
}

fn mentions_sorry(body: &str) -> bool {
    body.split(|c: char| !c.is_alphanumeric() && c != '_').any(|t| t == "sorry")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The shape every `Theorems/Thm_<name>.lean` in the FLT corpus has: one
    /// theorem, statement inline, proof delegated.
    const FLT: &str = r#"import Mathlib.Algebra.Algebra.Basic
import P2M.Sol.S_Algebra_norm_of_subsingleton

/-- The norm of an element of a subsingleton algebra is one. -/
theorem Algebra.norm_of_subsingleton {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [Subsingleton A] (a : A) : Algebra.norm R a = 1 := by
  p2m_exact_reverting @_root_.P2MW.S_Algebra_norm_of_subsingleton.solution
"#;

    #[test]
    fn reads_one_flt_theorem() {
        let d = scan(FLT).decls;
        assert_eq!(d.len(), 1);
        let d = &d[0];
        assert_eq!(d.name.as_str(), "Algebra.norm_of_subsingleton");
        assert_eq!(d.kind, "theorem");
        assert!(d.statement.contains("Algebra.norm R a = 1"));
        assert!(!d.statement.contains("p2m_exact_reverting"), "the proof is not the statement");
        assert_eq!(
            d.doc.as_deref(),
            Some("The norm of an element of a subsingleton algebra is one.")
        );
        assert_eq!((d.line_start, d.line_end), (5, 7));
    }

    #[test]
    fn imports_are_read_from_the_header_only() {
        assert_eq!(
            imports(FLT),
            vec![
                ModuleName::new("Mathlib.Algebra.Algebra.Basic"),
                ModuleName::new("P2M.Sol.S_Algebra_norm_of_subsingleton"),
            ]
        );
        // An `import` word inside a proof body must not be picked up.
        assert!(imports("theorem a : True := by\n  trivial\nimport Nope").is_empty());
    }

    #[test]
    fn identifiers_keep_the_global_ones_and_drop_bound_variables() {
        let ids = scan(FLT).decls[0].idents.iter().map(|i| i.to_string()).collect::<Vec<_>>();
        assert!(ids.contains(&"Algebra.norm".to_string()));
        assert!(ids.contains(&"CommRing".to_string()));
        assert!(!ids.contains(&"a".to_string()), "`a` is a bound variable");
    }

    #[test]
    fn namespaces_qualify_and_close() {
        let src = "namespace Foo\n\ntheorem bar : True := trivial\n\nend Foo\n\ntheorem baz : True := trivial\n";
        let names: Vec<String> = scan(src).decls.iter().map(|d| d.name.to_string()).collect();
        assert_eq!(names, vec!["Foo.bar", "baz"]);
    }

    #[test]
    fn an_anonymous_instance_is_not_given_the_namespace_as_its_name() {
        // Both of these are `instance : ...` with no name. Qualifying an empty
        // base produced `InverseLimit.` for each, so the second silently
        // replaced the first in the index: 229 of FLT's declarations vanished
        // this way.
        let src = "namespace InverseLimit\ninstance : Add Nat := inferInstance\ninstance [Foo] : Mul Nat := inferInstance\ninstance named : Sub Nat := inferInstance\nend InverseLimit\n";
        let names: Vec<String> = scan(src).decls.iter().map(|d| d.name.to_string()).collect();
        assert_eq!(names, vec!["InverseLimit.named"]);
    }

    #[test]
    fn modifiers_before_the_keyword_do_not_hide_a_declaration() {
        let src = "noncomputable def f : Nat := 0\nprivate theorem g : True := trivial\n";
        let kinds: Vec<String> = scan(src).decls.iter().map(|d| d.kind.clone()).collect();
        assert_eq!(kinds, vec!["def", "theorem"]);
    }

    #[test]
    fn a_nested_declaration_inside_a_proof_is_not_a_declaration() {
        let src = "theorem outer : True := by\n  have inner : True := trivial\n  exact inner\n";
        assert_eq!(scan(src).decls.len(), 1);
    }

    #[test]
    fn sorry_is_detected_but_not_inside_a_longer_word() {
        assert!(scan("theorem a : True := by\n  sorry\n").decls[0].has_sorry);
        assert!(!scan("theorem a : True := by\n  exact sorryFree\n").decls[0].has_sorry);
    }

    #[test]
    fn a_multi_declaration_file_gets_correct_line_ranges() {
        let src = "theorem a : True :=\n  trivial\n\ntheorem b : True :=\n  trivial\n";
        let d = scan(src).decls;
        assert_eq!(d.len(), 2);
        assert_eq!((d[0].line_start, d[0].line_end), (1, 2));
        assert_eq!((d[1].line_start, d[1].line_end), (4, 5));
    }
}
