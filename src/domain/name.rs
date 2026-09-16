//! The two names everything is keyed by. Both are dot-separated Lean names,
//! but they behave differently enough to be worth separating: a module maps to
//! a file, a declaration does not.

use std::fmt;
use std::path::PathBuf;

/// A fully qualified declaration name, e.g. `Real.exp_le_exp`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeclName(String);

impl DeclName {
    pub fn new(s: impl Into<String>) -> Self {
        DeclName(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }

    /// `Real.exp_le_exp` → `Real`.
    pub fn namespace(&self) -> Option<&str> {
        self.0.rsplit_once('.').map(|(ns, _)| ns)
    }

    /// `Mathlib.Order.Filter.Basic.foo` → `Mathlib`, and a name with no
    /// namespace at all → itself. The outermost namespace rather than the
    /// innermost, because that is the part a corpus owns.
    pub fn namespace_root(&self) -> &str {
        self.0.split_once('.').map_or(&self.0, |(root, _)| root)
    }

    /// The words of an argument that is several names the shell passed as
    /// one, or `None` for an argument that can be a name.
    ///
    /// No Lean name has whitespace outside `«»`. An argument that does was
    /// joined by the shell, and the usual way is a prime: in an unquoted line,
    /// `List.range'_one List.mem_range'_1` is one quoted string between the two
    /// primes, handed over without them.
    pub fn glued(arg: &str) -> Option<Vec<&str>> {
        let mut depth = 0usize;
        let spaced = arg.chars().any(|c| {
            match c {
                '«' => depth += 1,
                '»' => depth = depth.saturating_sub(1),
                _ => {}
            }
            depth == 0 && c.is_whitespace()
        });
        spaced.then(|| arg.split_whitespace().collect())
    }

    /// `Real.exp_le_exp` → `exp_le_exp`.
    pub fn base(&self) -> &str {
        self.0.rsplit_once('.').map_or(&self.0, |(_, b)| b)
    }

    /// Names Lean generates and nobody searches for. The dump filters these
    /// too; the check is repeated here because the text scanner has no
    /// elaborator to ask.
    pub fn is_internal(&self) -> bool {
        const GENERATED: &[&str] = &[
            "rec",
            "recOn",
            "casesOn",
            "below",
            "brecOn",
            "binductionOn",
            "ibelow",
            "ndrec",
            "ndrecOn",
            "noConfusion",
            "noConfusionType",
            "toCtorIdx",
            "injEq",
            "inj",
            "eq_def",
            "sizeOf_spec",
            "sizeOf_inst",
        ];
        self.0.is_empty()
            || self.0.starts_with('_')
            || self.0.contains("._")
            || self.0.contains("_@.")
            || GENERATED.contains(&self.base())
            || generated_with_index(self.base())
    }
}

/// `foo.eq_1`, `foo.proof_3`, `foo.match_2`: Lean numbers what it generates.
///
/// The number is the whole distinction. Matching the prefix alone also removes
/// `eq_comm`, `eq_sub_iff_add_eq` and every other lemma a person named after
/// the equation it is about — 703 of them in one corpus.
fn generated_with_index(base: &str) -> bool {
    ["eq_", "proof_", "match_"].iter().any(|p| {
        base.strip_prefix(p).is_some_and(|n| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
    })
}

impl fmt::Display for DeclName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for DeclName {
    fn from(s: &str) -> Self {
        DeclName::new(s)
    }
}

impl From<String> for DeclName {
    fn from(s: String) -> Self {
        DeclName(s)
    }
}

/// A Lean module, e.g. `Mathlib.Analysis.Complex.Exponential`. This is the name
/// that goes into an `import` line, and the one that maps to a file.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleName(String);

impl ModuleName {
    pub fn new(s: impl Into<String>) -> Self {
        ModuleName(s.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// The `import` line that actually provides the declaration. This is the
    /// real value of `dt show`: `Real.exp_le_exp` lives in
    /// `Mathlib.Analysis.Complex.Exponential`, not in the
    /// `Mathlib.Analysis.SpecialFunctions.Exp` one would guess.
    pub fn import_line(&self) -> String {
        format!("import {}", self.0)
    }

    /// `Mathlib.Analysis.Complex.Exponential` → `Mathlib/Analysis/Complex/Exponential.lean`,
    /// relative to the source root.
    pub fn relative_path(&self) -> PathBuf {
        let mut p = PathBuf::new();
        for part in self.0.split('.') {
            p.push(part);
        }
        p.set_extension("lean");
        p
    }

    /// The inverse of [`Self::relative_path`], for the text scanner which
    /// starts from a path and has no environment to ask.
    pub fn from_relative_path(p: &std::path::Path) -> Option<ModuleName> {
        let mut parts = Vec::new();
        for c in p.components() {
            parts.push(c.as_os_str().to_str()?.to_string());
        }
        let last = parts.last_mut()?;
        *last = last.strip_suffix(".lean")?.to_string();
        Some(ModuleName(parts.join(".")))
    }

    /// Whether the module is `prefix` itself or sits under it. Used by both the
    /// dump filter and `dt find --in`.
    pub fn is_under(&self, prefix: &str) -> bool {
        prefix.is_empty()
            || self.0 == prefix
            || (self.0.starts_with(prefix) && self.0.as_bytes().get(prefix.len()) == Some(&b'.'))
    }
}

impl fmt::Display for ModuleName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<&str> for ModuleName {
    fn from(s: &str) -> Self {
        ModuleName::new(s)
    }
}

impl From<String> for ModuleName {
    fn from(s: String) -> Self {
        ModuleName(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_argument_with_spaces_is_names_the_shell_joined() {
        assert_eq!(
            DeclName::glued("List.range_one List.Perm.mem_iff List.mem_range_1"),
            Some(vec!["List.range_one", "List.Perm.mem_iff", "List.mem_range_1"])
        );
        assert_eq!(DeclName::glued("List.range'_one"), None);
        assert_eq!(DeclName::glued("Foo.«a b»"), None, "a guillemet name may have a space");
    }
    use std::path::Path;

    #[test]
    fn splits_a_declaration_name() {
        let n = DeclName::new("Real.exp_le_exp");
        assert_eq!(n.namespace(), Some("Real"));
        assert_eq!(n.base(), "exp_le_exp");

        let bare = DeclName::new("Nat");
        assert_eq!(bare.namespace(), None);
        assert_eq!(bare.base(), "Nat");
    }

    #[test]
    fn recognises_generated_names() {
        for n in [
            "Nat.rec",
            "Foo.casesOn",
            "Foo.proof_1",
            "_private.Mathlib.X",
            "Foo.injEq",
            "Foo.eq_1",
            "Foo.eq_def",
            "Foo.match_2",
        ] {
            assert!(DeclName::new(n).is_internal(), "{n} should be internal");
        }
        // `eq_` is a prefix people use. Treating it as generated removed every
        // lemma named after the equation it is about.
        for n in [
            "Real.exp_le_exp",
            "Finset.sum_le_sum",
            "Nat",
            "eq_comm",
            "eq_sub_iff_add_eq",
            "Foo.eq_originIdeal_of_mem",
            "Foo.match_left",
            "proof_irrel",
        ] {
            assert!(!DeclName::new(n).is_internal(), "{n} should be kept");
        }
    }

    #[test]
    fn maps_a_module_to_a_path_and_back() {
        let m = ModuleName::new("Mathlib.Analysis.Complex.Exponential");
        assert_eq!(m.relative_path(), Path::new("Mathlib/Analysis/Complex/Exponential.lean"));
        assert_eq!(ModuleName::from_relative_path(&m.relative_path()), Some(m));
    }

    #[test]
    fn import_line_is_the_module_not_the_path() {
        assert_eq!(
            ModuleName::new("Mathlib.Analysis.Complex.Exponential").import_line(),
            "import Mathlib.Analysis.Complex.Exponential"
        );
    }

    #[test]
    fn prefix_matching_respects_component_boundaries() {
        let m = ModuleName::new("Mathlib.Analysis.Complex");
        assert!(m.is_under("Mathlib"));
        assert!(m.is_under("Mathlib.Analysis"));
        assert!(m.is_under("Mathlib.Analysis.Complex"));
        assert!(m.is_under(""));
        // `Mathlib.Analysis` must not be matched by the prefix `Mathlib.Ana`.
        assert!(!m.is_under("Mathlib.Ana"));
        assert!(!m.is_under("Batteries"));
    }
}
