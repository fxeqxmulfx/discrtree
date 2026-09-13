//! Dependency closure and the frontier.
//!
//! The obvious design for lifting a declaration — print it and its transitive
//! dependencies — does not survive contact with the numbers: `Real.exp_le_exp`
//! is a two-line lemma resting on 5154 declarations, because `Real.exp` is
//! built on the whole Cauchy-sequence and complex-analysis tower.
//!
//! So the raw closure is never the deliverable. What makes the tree tractable
//! is not a depth cap but the `importable` flag: a dependency from an
//! importable source collapses to one `import` line and its entire subtree
//! disappears with it. What remains is the frontier, and the frontier is what
//! gets materialized.

use crate::domain::decl::Decl;
use crate::domain::name::{DeclName, ModuleName};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// How the closure walk reads the corpus. A trait rather than a map so that
/// `dt deps --depth 1` can answer from one lookup instead of loading 5154 rows.
pub trait DeclSource {
    fn get(&self, name: &DeclName) -> Option<Decl>;
    /// Whether a dependency on this declaration collapses into an import.
    fn is_importable(&self, d: &Decl) -> bool;
}

/// A closure walk, cycle-safe, with the importable frontier already collapsed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Frontier {
    /// Import lines that replace whole subtrees.
    pub imports: BTreeSet<ModuleName>,
    /// Declarations that have to be copied, in dependency order: a declaration
    /// never appears before something it needs.
    pub materialize: Vec<DeclName>,
    /// Names nothing in the index knows. A non-empty list means the answer is
    /// incomplete, and the caller must say so.
    pub missing: BTreeSet<DeclName>,
    /// Depth of the materialization tree. Data, not an assumption: one file for
    /// one source and a deep tree for another.
    pub depth: usize,
    /// Set when any node came from a source whose dependencies are guessed from
    /// text rather than read off a proof term.
    pub approximate: bool,
}

impl Frontier {
    pub fn is_trivial(&self) -> bool {
        self.materialize.is_empty()
    }
}

/// Resolve the frontier for `roots`.
///
/// An importable node contributes its module as an import and is not descended
/// into — that is the whole point. A non-importable node is materialized and
/// its dependencies are followed.
pub fn frontier(roots: &[DeclName], src: &dyn DeclSource) -> Frontier {
    let mut f = Frontier::default();
    let mut depth_of: BTreeMap<DeclName, usize> = BTreeMap::new();
    let mut seen: BTreeSet<DeclName> = BTreeSet::new();
    // Nodes to materialize, in the order they were first reached, plus their
    // dependency edges, so the result can be sorted topologically at the end.
    let mut edges: BTreeMap<DeclName, Vec<DeclName>> = BTreeMap::new();
    let mut queue: VecDeque<(DeclName, usize)> = roots.iter().cloned().map(|n| (n, 0)).collect();

    while let Some((name, depth)) = queue.pop_front() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(decl) = src.get(&name) else {
            f.missing.insert(name);
            continue;
        };
        // An importable node contributes its module and is not descended into,
        // roots included. A Lean module cannot compile without importing what
        // its own declarations use, so that one import carries the whole
        // subtree: walking it anyway would emit an import line for each
        // dependency that the first import already provides.
        if src.is_importable(&decl) {
            f.imports.insert(decl.module.clone());
            continue;
        }
        if !decl.elaborated {
            f.approximate = true;
        }
        depth_of.insert(name.clone(), depth);
        f.depth = f.depth.max(depth);
        let deps: Vec<DeclName> = decl.deps.iter().filter(|d| **d != name).cloned().collect();
        for d in &deps {
            queue.push_back((d.clone(), depth + 1));
        }
        edges.insert(name, deps);
    }

    f.materialize = topological(&edges);
    f
}

/// Dependencies first, cycles broken at whatever edge closes them. Lean forbids
/// cyclic definitions, but an approximated dependency graph can invent one, and
/// a tool that hangs on bad input is worse than one that emits a suspect order.
fn topological(edges: &BTreeMap<DeclName, Vec<DeclName>>) -> Vec<DeclName> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mark {
        Open,
        Done,
    }
    let mut mark: BTreeMap<&DeclName, Mark> = BTreeMap::new();
    let mut out = Vec::with_capacity(edges.len());
    // An explicit stack: a frontier can be thousands deep, and the recursive
    // form would overflow on exactly the inputs this exists for.
    for root in edges.keys() {
        if mark.contains_key(root) {
            continue;
        }
        let mut stack = vec![(root, 0usize)];
        while let Some((node, i)) = stack.pop() {
            if i == 0 {
                if mark.contains_key(node) {
                    continue;
                }
                mark.insert(node, Mark::Open);
            }
            match edges.get(node).and_then(|d| d.get(i)) {
                Some(dep) => {
                    stack.push((node, i + 1));
                    if let Some((k, _)) = edges.get_key_value(dep)
                        && !mark.contains_key(k)
                    {
                        stack.push((k, 0));
                    }
                }
                None => {
                    mark.insert(node, Mark::Done);
                    out.push(node.clone());
                }
            }
        }
    }
    out
}

/// One level of `dt deps`: the direct dependencies, each still tagged by source.
/// Depth 1-2 is the readable regime and answers "what does this proof rest on".
pub fn levels(root: &DeclName, src: &dyn DeclSource, depth: usize) -> Vec<Vec<Decl>> {
    let mut seen: BTreeSet<DeclName> = BTreeSet::from([root.clone()]);
    let mut out = Vec::new();
    let mut current: Vec<DeclName> = match src.get(root) {
        Some(d) => d.deps.clone(),
        None => return out,
    };
    for _ in 0..depth {
        if current.is_empty() {
            break;
        }
        let mut resolved = Vec::new();
        let mut next = Vec::new();
        for name in current {
            if !seen.insert(name.clone()) {
                continue;
            }
            if let Some(d) = src.get(&name) {
                next.extend(d.deps.iter().cloned());
                resolved.push(d);
            }
        }
        if resolved.is_empty() {
            break;
        }
        resolved.sort_by(|a, b| a.name.cmp(&b.name));
        out.push(resolved);
        current = next;
    }
    out
}

/// The size of the full closure, for `--depth all`, which prints a count first
/// and the list only when asked again.
pub fn closure_size(root: &DeclName, src: &dyn DeclSource) -> ClosureStats {
    let mut seen = BTreeSet::new();
    let mut theorems = 0;
    let mut by_source: BTreeMap<String, usize> = BTreeMap::new();
    let mut queue = VecDeque::from([root.clone()]);
    while let Some(n) = queue.pop_front() {
        if !seen.insert(n.clone()) {
            continue;
        }
        if let Some(d) = src.get(&n) {
            // The root is what was asked about, not one of its own
            // dependencies, so it is counted in neither the total nor the
            // breakdown — otherwise the columns do not add up to the number
            // printed above them.
            if &n != root {
                if d.kind.is_proposition() {
                    theorems += 1;
                }
                *by_source.entry(d.source.to_string()).or_default() += 1;
            }
            queue.extend(d.deps.iter().cloned());
        }
    }
    seen.remove(root);
    ClosureStats { total: seen.len(), theorems, by_source }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClosureStats {
    pub total: usize,
    pub theorems: usize,
    pub by_source: BTreeMap<String, usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::decl::DeclKind;
    use std::collections::HashMap;

    /// A corpus fixture: name -> (source, module, deps).
    struct Corpus {
        decls: HashMap<String, Decl>,
        importable: BTreeSet<String>,
    }

    impl Corpus {
        fn new(rows: &[(&str, &str, &str, &[&str])], importable: &[&str]) -> Corpus {
            let mut decls = HashMap::new();
            for (name, source, module, deps) in rows {
                let mut d = Decl::stub(name, source, module);
                d.deps = deps.iter().map(|s| DeclName::new(*s)).collect();
                d.elaborated = *source != "flt";
                decls.insert(name.to_string(), d);
            }
            Corpus { decls, importable: importable.iter().map(|s| s.to_string()).collect() }
        }
    }

    impl DeclSource for Corpus {
        fn get(&self, name: &DeclName) -> Option<Decl> {
            self.decls.get(name.as_str()).cloned()
        }
        fn is_importable(&self, d: &Decl) -> bool {
            self.importable.contains(d.source.as_str())
        }
    }

    fn n(s: &str) -> DeclName {
        DeclName::new(s)
    }

    #[test]
    fn an_importable_dependency_collapses_its_whole_subtree() {
        // `root` (not importable) depends on a Mathlib lemma that itself rests
        // on a tower. None of the tower may be materialized.
        let c = Corpus::new(
            &[
                ("root", "flt", "Thm.Root", &["Mathlib.lemma"]),
                ("Mathlib.lemma", "mathlib", "Mathlib.A", &["Mathlib.deep"]),
                ("Mathlib.deep", "mathlib", "Mathlib.B", &[]),
            ],
            &["mathlib"],
        );
        let f = frontier(&[n("root")], &c);
        assert_eq!(f.materialize, vec![n("root")]);
        assert_eq!(f.imports, BTreeSet::from([ModuleName::new("Mathlib.A")]));
        assert!(f.approximate, "an flt row must mark the answer approximate");
    }

    #[test]
    fn a_mathlib_target_answers_with_one_import_and_nothing_to_copy() {
        let c = Corpus::new(
            &[
                ("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Complex.Exponential", &["x"]),
                ("x", "mathlib", "Mathlib.B", &[]),
            ],
            &["mathlib"],
        );
        let f = frontier(&[n("Real.exp_le_exp")], &c);
        assert_eq!(
            f.imports,
            BTreeSet::from([ModuleName::new("Mathlib.Analysis.Complex.Exponential")]),
            "one import is the whole answer: `Mathlib.B` is already behind it, \
             and listing it as well would be noise"
        );
        assert!(f.materialize.is_empty(), "nothing is copied out of an importable source");
        assert!(!f.approximate);
    }

    #[test]
    fn materialization_is_in_dependency_order() {
        let c = Corpus::new(
            &[("a", "flt", "M.A", &["b"]), ("b", "flt", "M.B", &["c"]), ("c", "flt", "M.C", &[])],
            &[],
        );
        let f = frontier(&[n("a")], &c);
        let pos = |x: &str| f.materialize.iter().position(|m| m.as_str() == x).unwrap();
        assert!(pos("c") < pos("b") && pos("b") < pos("a"));
        assert_eq!(f.depth, 2);
    }

    #[test]
    fn a_cycle_terminates_instead_of_hanging() {
        let c = Corpus::new(&[("a", "flt", "M.A", &["b"]), ("b", "flt", "M.B", &["a"])], &[]);
        let f = frontier(&[n("a")], &c);
        assert_eq!(f.materialize.len(), 2);
    }

    #[test]
    fn a_deep_chain_does_not_overflow_the_stack() {
        let names: Vec<String> = (0..5000).map(|i| format!("d{i}")).collect();
        let rows: Vec<(&str, &str, &str, Vec<&str>)> = (0..5000)
            .map(|i| {
                let deps: Vec<&str> =
                    if i + 1 < 5000 { vec![names[i + 1].as_str()] } else { vec![] };
                (names[i].as_str(), "flt", "M.X", deps)
            })
            .collect();
        let owned: Vec<(&str, &str, &str, &[&str])> =
            rows.iter().map(|(a, b, c, d)| (*a, *b, *c, d.as_slice())).collect();
        let c = Corpus::new(&owned, &[]);
        let f = frontier(&[n("d0")], &c);
        assert_eq!(f.materialize.len(), 5000);
        assert_eq!(f.materialize.first().map(|x| x.as_str()), Some("d4999"));
    }

    #[test]
    fn unknown_names_are_reported_not_silently_dropped() {
        let c = Corpus::new(&[("a", "flt", "M.A", &["ghost"])], &[]);
        let f = frontier(&[n("a")], &c);
        assert_eq!(f.missing, BTreeSet::from([n("ghost")]));
    }

    #[test]
    fn levels_stop_at_the_requested_depth() {
        let c = Corpus::new(
            &[
                ("a", "mathlib", "M.A", &["b", "c"]),
                ("b", "mathlib", "M.B", &["d"]),
                ("c", "mathlib", "M.C", &[]),
                ("d", "mathlib", "M.D", &[]),
            ],
            &["mathlib"],
        );
        let one = levels(&n("a"), &c, 1);
        assert_eq!(one.len(), 1);
        assert_eq!(one[0].iter().map(|d| d.name.to_string()).collect::<Vec<_>>(), ["b", "c"]);
        assert_eq!(levels(&n("a"), &c, 5).len(), 2);
    }

    #[test]
    fn closure_size_counts_theorems_separately() {
        let mut c = Corpus::new(
            &[
                ("a", "mathlib", "M.A", &["b", "c"]),
                ("b", "mathlib", "M.B", &[]),
                ("c", "mathlib", "M.C", &[]),
            ],
            &["mathlib"],
        );
        c.decls.get_mut("c").unwrap().kind = DeclKind::Def;
        let s = closure_size(&n("a"), &c);
        // The root is excluded from every one of the three, so the breakdown
        // adds up to the total that is printed above it.
        assert_eq!(s.total, 2);
        assert_eq!(s.theorems, 1); // `b`; `c` is a def and `a` is the root
        assert_eq!(s.by_source.get("mathlib"), Some(&2));
    }
}
