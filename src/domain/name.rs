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
            || self.base().starts_with("proof_")
            || self.base().starts_with("eq_")
            || self.base().starts_with("match_")
    }
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
        for n in ["Nat.rec", "Foo.casesOn", "Foo.proof_1", "_private.Mathlib.X", "Foo.injEq"] {
            assert!(DeclName::new(n).is_internal(), "{n} should be internal");
        }
        for n in ["Real.exp_le_exp", "Finset.sum_le_sum", "Nat"] {
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
