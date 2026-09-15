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
    // The module system's, and a declaration modifier like any other:
    // `public theorem` is a theorem. `public import` is not a declaration, and
    // is not one after this either -- `import` is structural.
    "public ",
    // The module system's other one: `meta def evalSqrt` is a `def` that runs
    // at elaboration time, and `positivity` extensions are written that way.
    "meta ",
    "protected ",
    "noncomputable ",
    "partial ",
    "unsafe ",
    "nonrec ",
    "scoped ",
    "local ",
];

/// Whether a slice of source declares anything at all.
///
/// Lean's declaration range for a *generated* declaration points at the syntax
/// that generated it, which is not a declaration: `to_additive` points at its
/// own attribute block, a structure field at the field line. Printing those
/// lines and calling them the declaration is the one thing `dt show` exists to
/// prevent, so it has to be able to tell.
pub fn declares(text: &str) -> bool {
    code_lines(text).any(|l| header(l).is_some())
}

/// The lines of a range that are code: not inside a block comment, and not a
/// line comment.
///
/// A range that declares nothing is usually made of comments, and a comment can
/// hold anything — a doc comment explaining a theorem, prose at column zero,
/// an attribute block with a docstring inside it. Reading those as syntax is
/// how `@[to_additive /-- sums over ... -/]` would come to declare something.
fn code_lines(text: &str) -> impl Iterator<Item = &str> {
    let mut depth = 0usize;
    text.lines().filter(move |l| {
        let opened = depth;
        depth = comment_depth(l, depth);
        let t = l.trim_start();
        // A line that opens a comment is the one the depth does not yet cover,
        // and it is where a docstring starts. Nothing declares anything at a
        // `/-`, so dropping the whole line costs nothing and keeps `/-- The
        // Bochner integral -/` out of the answer.
        opened == 0 && !t.starts_with("--") && !t.starts_with("/-")
    })
}

/// The block comment nesting a line leaves behind. Lean's `/- -/` nests, and
/// `/--` is a `/-` like any other.
fn comment_depth(line: &str, mut depth: usize) -> usize {
    let b = line.as_bytes();
    let mut i = 0;
    while i + 1 < b.len() {
        match (b[i], b[i + 1]) {
            (b'/', b'-') => {
                depth += 1;
                i += 2;
            }
            (b'-', b'/') => {
                depth = depth.saturating_sub(1);
                i += 2;
            }
            _ => i += 1,
        }
    }
    depth
}

/// Whether a slice of source declares `name` in particular.
///
/// `declares` only says the lines declare something. A structure's constructor
/// is given the range of a line of the structure, so those lines do declare
/// something, and it is not the row in hand: `MonoidHom.mk` points at
/// `structure MonoidHom ...`. The name in the header is what separates the two.
/// An anonymous `instance : Foo Bar` has no name to compare and is taken at its
/// word, since nothing else in the file claims that line either.
pub fn declares_name(text: &str, name: &DeclName) -> bool {
    code_lines(text).any(|l| match header(l) {
        Some((_, rest)) => {
            let bound = bound(rest);
            bound.is_empty() || bound.iter().any(|id| names(id, name))
        }
        None => commands(l, name),
    })
}

/// Whether a header's identifier is this declaration. Lean prints the name in
/// full and the file writes whatever suffix of it the surrounding namespaces
/// leave: `Matroid.IsRkFinite.diff_singleton_iff` is written
/// `IsRkFinite.diff_singleton_iff` inside `namespace Matroid`. `_root_.` is the
/// opposite instruction -- ignore the namespaces -- and either way the name
/// that follows it is a suffix of the full one.
fn names(id: &str, name: &DeclName) -> bool {
    let id = id.strip_prefix("_root_.").unwrap_or(id);
    let full = name.as_str();
    full == id || full.strip_suffix(id).is_some_and(|ns| ns.ends_with('.'))
}

/// The names a header binds: the identifier it opens with, or, for the
/// `alias ⟨mp, mpr⟩ := iff` form, both of them. Empty where the header goes
/// straight into binders or the type -- an anonymous instance.
fn bound(rest: &str) -> Vec<&str> {
    let rest = rest.trim_start();
    match rest.strip_prefix('⟨').and_then(|r| r.split_once('⟩')) {
        Some((inner, _)) => inner.split(',').map(str::trim).collect(),
        None => ident(rest).into_iter().collect(),
    }
}

/// Whether the line is a declaration command this does not know, declaring
/// exactly this name.
///
/// [`HEADERS`] is what a scan with no name in hand can recognise, and it cannot
/// grow to cover Lean: `irreducible_def`, and every other command a library
/// defines for itself, produce declarations that list will never have. Asking
/// whether a known range holds a known name is a different question, and for
/// that one the command word does not have to be known — a word at column zero
/// followed by the name is that name's header, whatever the word is.
///
/// `MeasureTheory.integral` is the case this was written for: its range is the
/// five lines of `irreducible_def integral ...`, and `dt show` called them a
/// docstring that declares nothing.
fn commands(line: &str, name: &DeclName) -> bool {
    let Some(rest) = undecorated(line) else { return false };
    let Some(word) = rest.split([' ', '\t']).next() else { return false };
    if !word.starts_with(|c: char| c.is_ascii_lowercase())
        || !word.chars().all(|c| c.is_alphanumeric() || "_!?'".contains(c))
        || STRUCTURAL.contains(&word)
    {
        return false;
    }
    bound(&rest[word.len()..]).iter().any(|id| names(id, name))
}

/// The commands that take a name at column zero and do not declare it. Unlike
/// the declaration commands, this list is closed: a library can add a way to
/// declare something, and cannot add a way to open a namespace.
const STRUCTURAL: &[&str] = &[
    "end",
    "namespace",
    "section",
    "open",
    "universe",
    "variable",
    "variables",
    "import",
    "export",
    "attribute",
    "set_option",
    "deriving",
];

/// The first line of a range that is neither blank nor a comment, falling back
/// to the first line that is not blank.
///
/// What a range holds, when it does not hold the declaration. A doc comment is
/// the one thing it must not be: quoting `/-- The Bochner integral -/` back at
/// someone who asked for `MeasureTheory.integral` names the declaration they
/// asked about and says nothing about why its source is not here.
pub fn first_code_line(text: &str) -> &str {
    code_lines(text)
        .map(str::trim)
        .find(|l| !l.is_empty())
        .or_else(|| text.lines().map(str::trim).find(|l| !l.is_empty()))
        .unwrap_or("")
}

/// The identifier a declaration header opens with, or `None` where the header
/// goes straight into binders or the type — an anonymous instance.
fn ident(rest: &str) -> Option<&str> {
    let id = rest.trim_start().split([' ', '\t', '(', '{', '[', ':']).next()?;
    (!id.is_empty()).then_some(id)
}

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
    let rest = undecorated(line)?;
    let h = HEADERS.iter().find(|h| rest.starts_with(**h))?;
    Some((h.trim_end(), &rest[h.len()..]))
}

/// What is left of a line after the attributes and modifiers a declaration may
/// open with, or `None` when it is indented — a declaration starts at column
/// zero, and requiring it is what keeps a `have` inside a proof from reading as
/// one.
fn undecorated(line: &str) -> Option<&str> {
    if line.starts_with([' ', '\t']) {
        return None;
    }
    let mut rest = line;
    loop {
        if let Some(after) = attribute(rest) {
            rest = after;
            continue;
        }
        match MODIFIERS.iter().find(|m| rest.starts_with(**m)) {
            Some(m) => rest = &rest[m.len()..],
            None => return Some(rest),
        }
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
    fn an_attribute_block_declares_nothing() {
        // Exactly what Lean hands back as the range of `Finset.sum_image`: the
        // `to_additive` block above `theorem prod_image`, which is a different
        // declaration and begins on the line after the range ends.
        let block = "@[to_additive (attr := simp) /-- If a function is injective on a finset, sums\n                     over the original finset or its image coincide. -/]";
        assert!(!declares(block));
        assert!(!declares("  d_model : \u{2115}"), "a structure field is not a declaration");
        assert!(!declares(""));

        assert!(declares("theorem prod_image : True := trivial"));
        assert!(declares("@[simp] theorem f : True := trivial"), "an attribute may precede it");
        assert!(declares("private noncomputable def g : Nat := 0"), "so may modifiers");
        assert!(declares("/-- doc -/\ninstance : Nat := 0"), "the header may be on a later line");
    }

    #[test]
    fn a_structure_line_declares_the_structure_and_not_its_constructor() {
        // The range Lean gives `MonoidHom.mk` is one line of `structure
        // MonoidHom`, so the lines do declare something; the name is the only
        // thing that says it is something else.
        let line = "structure MonoidHom (M : Type*) (N : Type*) [MulOne M] [MulOne N] extends";
        assert!(declares(line), "the line does declare a structure");
        assert!(!declares_name(line, &DeclName::new("MonoidHom.mk")));
        assert!(declares_name(line, &DeclName::new("MonoidHom")));

        let thm = "@[simp] theorem exp_le_exp : True := trivial";
        assert!(declares_name(thm, &DeclName::new("Real.exp_le_exp")), "a namespace is dropped");
        assert!(declares_name(thm, &DeclName::new("exp_le_exp")));

        let full = "protected theorem Finset.sum_image {s : Finset α} : True := trivial";
        assert!(declares_name(full, &DeclName::new("Finset.sum_image")), "or spelled in full");

        let anon = "instance : Repr Nat.Primes :=\n  \u{27e8}fun p _ => repr p.val\u{27e9}";
        assert!(
            declares_name(anon, &DeclName::new("Nat.Primes.instRepr")),
            "an anonymous instance has no name to compare, and the line is still its source"
        );
    }

    #[test]
    fn a_command_this_does_not_know_still_declares_the_name_it_names() {
        // Mathlib's own `MeasureTheory.integral`, verbatim. `irreducible_def`
        // is not in HEADERS and never will be -- a library may define any
        // command it likes -- but the word at column zero is followed by the
        // name, and that is enough to say the range is the declaration.
        let src = "/-- The Bochner integral -/\nirreducible_def integral {_ : MeasurableSpace \u{3b1}} (\u{3bc} : Measure \u{3b1}) (f : \u{3b1} \u{2192} G) : G :=\n  if hG : CompleteSpace G then ... else 0";
        assert!(declares_name(src, &DeclName::new("MeasureTheory.integral")));
        assert!(!declares_name(src, &DeclName::new("MeasureTheory.integral_def")));

        let al = "alias FiniteDimensional.left := Module.Finite.left";
        assert!(declares_name(al, &DeclName::new("FiniteDimensional.left")));
        let ext = "meta def evalSqrt : PositivityExt where";
        assert!(declares_name(ext, &DeclName::new("Mathlib.Meta.Positivity.evalSqrt")));
        let pubthm = "public theorem foo : True := trivial";
        assert!(declares_name(pubthm, &DeclName::new("Bar.foo")));
    }

    #[test]
    fn a_command_that_does_not_declare_is_not_taken_for_one() {
        for line in ["namespace Real", "open Finset", "end Real", "export Nat", "variable Real"] {
            let name = DeclName::new(line.split(' ').nth(1).unwrap());
            assert!(!declares_name(line, &name), "{line}");
        }
        // Not a command at all: a line of a proof, which is indented.
        assert!(!declares_name("  exact foo", &DeclName::new("foo")));
    }

    #[test]
    fn the_namespace_a_file_leaves_implicit_is_not_part_of_the_name() {
        // `alias IsRkFinite.diff_singleton_iff := ...` inside `namespace
        // Matroid`: the file writes whatever suffix the namespaces leave, and
        // that suffix is more than the last component.
        let src = "@[deprecated (since := \"2026-06-03\")]\nalias IsRkFinite.diff_singleton_iff := IsRkFinite.sdiff_singleton_iff";
        assert!(declares_name(src, &DeclName::new("Matroid.IsRkFinite.diff_singleton_iff")));
        assert!(!declares_name(src, &DeclName::new("Matroid.IsRkFinite.sdiff_singleton_iff")));
        assert!(
            !declares_name(src, &DeclName::new("Matroid.diff_singleton_iff")),
            "a suffix is whole components"
        );

        // `_root_.` says to ignore the namespaces, and the name after it is the
        // whole of the one Lean prints.
        let root = "alias _root_.isSolvable_of_top_eq_bot := Group.isSolvable_of_top_eq_bot";
        assert!(declares_name(root, &DeclName::new("isSolvable_of_top_eq_bot")));
    }

    #[test]
    fn an_alias_binds_both_halves_of_an_iff() {
        let one = "protected alias \u{27e8}_, biUnion\u{27e9} := Set.Finite.absorbs_biUnion";
        assert!(declares_name(one, &DeclName::new("Absorbs.biUnion")));
        assert!(!declares_name(one, &DeclName::new("Absorbs.absorbs_biUnion")));

        let both =
            "alias \u{27e8}LowerSemicontinuous.le_liminf, of_le_liminf\u{27e9} := iff_le_liminf";
        assert!(declares_name(both, &DeclName::new("LowerSemicontinuous.le_liminf")));
        assert!(declares_name(both, &DeclName::new("LowerSemicontinuous.of_le_liminf")));
    }

    #[test]
    fn a_comment_is_not_read_as_syntax() {
        // A docstring may hold anything, including prose at column zero that
        // reads like a command.
        let doc = "/-- theorem foo says that\ninstance Bar is a Baz. -/\n";
        assert!(!declares(doc));
        assert!(!declares_name(doc, &DeclName::new("foo")));
        assert!(!declares("-- def f : Nat := 0"));
        // `/- -/` nests, and `/--` is a `/-` like any other.
        assert!(!declares("/- outer /- inner -/ theorem f : True := trivial -/"));
        assert!(declares("/- a -/\ntheorem f : True := trivial"), "and the block does end");
    }

    #[test]
    fn the_head_of_a_range_is_its_first_line_of_code() {
        // What `dt show` prints when the range holds no declaration. A
        // docstring is the one thing it must not be: quoting the declaration's
        // own documentation back names it and says nothing about why its source
        // is not here.
        let src = "/-- The Bochner integral -/\nirreducible_def integral (\u{3bc} : Measure \u{3b1}) : G :=";
        assert_eq!(
            first_code_line(src),
            "irreducible_def integral (\u{3bc} : Measure \u{3b1}) : G :="
        );
        assert_eq!(first_code_line("\n\n@[to_additive]\n"), "@[to_additive]");
        assert_eq!(
            first_code_line("/-- all of it -/"),
            "/-- all of it -/",
            "a range with nothing else falls back to it"
        );
        assert_eq!(first_code_line(""), "");
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
