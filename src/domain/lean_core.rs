//! What the toolchain's own library declares, as far as a name can tell.
//!
//! Core is the one corpus with no directory to read. A lake package announces
//! itself by sitting under `.lake/packages`, so what it provides can be walked;
//! core ships inside the toolchain, and the modules that would say what it
//! declares are exactly the ones that were never dumped. So the knowledge is
//! written down here instead, and it is knowledge about Lean rather than about
//! any machine, which is why it lives in the domain.

/// The module roots the toolchain's library provides. What a source would have
/// to `import` to dump it, and what an `--in` filter would have to name.
pub const ROOTS: &[&str] = &["Init", "Std", "Lean"];

/// Root namespaces core declares in.
///
/// Not the same list as [`ROOTS`] and that is the whole difficulty:
/// `Int.add_one_le_iff` is declared in module `Init.Data.Int.Order`, so the
/// module root is `Init` and the namespace root is `Int`, and a name is all
/// `dt show` has to go on.
///
/// Held to the types core defines and proves about — the ones Mathlib imports
/// and mostly only uses. Namespaces the two share heavily (`Function`, `Set`,
/// `Finset`) are left out: the point is to explain a `no match`, and an
/// explanation that fits every missing name explains nothing.
pub const NAMESPACES: &[&str] = &[
    "Array",
    "BitVec",
    "Bool",
    "ByteArray",
    "Char",
    "Decidable",
    "Except",
    "Fin",
    "Float",
    "IO",
    "Init",
    "Int",
    "Lean",
    "List",
    "Nat",
    "Option",
    "Ord",
    "Ordering",
    "Prod",
    "Quot",
    "Quotient",
    "Std",
    "String",
    "Subarray",
    "Substring",
    "Sum",
    "System",
    "UInt16",
    "UInt32",
    "UInt64",
    "UInt8",
    "USize",
    "Vector",
];

/// Whether core declares in this name's root namespace.
///
/// A guess, and deliberately a weak one: it says the namespace is core's, not
/// that the declaration is. That is enough to stop a reader concluding a lemma
/// does not exist, and claiming more would be claiming to know what is in a
/// corpus nobody has read.
pub fn declares(name: &str) -> bool {
    NAMESPACES.contains(&name.split('.').next().unwrap_or(name))
}

/// Whether this module prefix is one of core's roots or something under one.
pub fn has_module(prefix: &str) -> bool {
    ROOTS.iter().any(|r| prefix == *r || prefix.strip_prefix(r).is_some_and(|s| s.starts_with('.')))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_namespace_is_matched_by_its_root_not_by_its_spelling() {
        assert!(declares("Int.add_one_le_iff"));
        assert!(declares("List.Perm.length_eq"));
        assert!(declares("Nat"));
        // `Interval` starts with `Int` and is Mathlib's.
        assert!(!declares("Interval.mem_iff"));
        assert!(!declares("Finset.sum_image"));
        assert!(!declares("Real.exp_le_exp"));
    }

    #[test]
    fn a_module_root_is_not_a_namespace_root() {
        // The asymmetry the whole file exists for: the module says `Init`, the
        // name says `Int`, and neither can be derived from the other.
        assert!(has_module("Init.Data.Int.Order"));
        assert!(has_module("Std.Data.HashMap"));
        assert!(!has_module("Int"));
        assert!(!has_module("Initial.Objects"));
        assert!(!has_module("Mathlib.Data.Int.Order"));
    }
}
