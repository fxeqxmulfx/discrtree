//! What `dt add --write` puts on disk.
//!
//! Materialized Mathlib or FLT code is somebody else's, under somebody else's
//! licence. The provenance header is a requirement, not decoration: it names
//! the source, the upstream path, the revision and the licence, so the origin
//! of every vendored line is readable from the file itself.

use crate::domain::decl::Decl;
use crate::domain::name::ModuleName;
use crate::domain::source::{SourceId, SourceMeta};
use std::collections::BTreeMap;
use std::path::PathBuf;

/// One file `dt add --write` would create, with everything needed to write it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VendorFile {
    /// Path under `[project] vendor`.
    pub path: PathBuf,
    /// The module name that path will have once it is in the project, which is
    /// also what has to be added to the aggregator.
    pub module: ModuleName,
    /// Imports the file needs, already collapsed.
    pub imports: Vec<ModuleName>,
    /// Provenance header, without a trailing newline.
    pub header: String,
    /// Declarations that go into it, in dependency order.
    pub decls: Vec<Decl>,
}

impl VendorFile {
    pub fn lines(&self) -> usize {
        self.decls.iter().map(|d| d.span.map_or(0, |s| s.lines() as usize)).sum()
    }
}

/// The whole write, reported before anything is written. The dry run exists
/// precisely because depth cannot be predicted from the name.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct VendorPlan {
    pub files: Vec<VendorFile>,
    /// Import lines added to the project's aggregator.
    pub imports: Vec<ModuleName>,
    /// Declarations per source, for the dry-run report.
    pub by_source: BTreeMap<SourceId, usize>,
}

impl VendorPlan {
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }

    pub fn total_lines(&self) -> usize {
        self.files.iter().map(VendorFile::lines).sum()
    }

    pub fn total_decls(&self) -> usize {
        self.files.iter().map(|f| f.decls.len()).sum()
    }
}

/// The provenance header for a vendored module.
pub fn provenance_header(
    meta: Option<&SourceMeta>,
    source: &SourceId,
    origin: &ModuleName,
) -> String {
    let mut out =
        String::from("/-\nVendored by `dt add`. Do not edit: re-run `dt add` instead.\n\n");
    out.push_str(&format!("Source:   {source}\n"));
    out.push_str(&format!("Upstream: {}\n", origin.relative_path().display()));
    if let Some(m) = meta {
        if let Some(rev) = &m.rev {
            out.push_str(&format!("Revision: {rev}\n"));
        }
        if let Some(l) = &m.license {
            out.push_str(&format!("Licence:  {l}\n"));
        }
        if let Some(a) = &m.attribution {
            out.push_str(&format!("Credit:   {a}\n"));
        }
    }
    out.push_str("-/");
    out
}

/// Group the materialization set into files, one per origin module.
///
/// Per module rather than per declaration: it keeps the vendored source
/// readable and diffable against upstream, at the cost of copying a declaration
/// nothing asked for when two from one module are needed. The alternative is
/// recorded in the plan's open questions; decide it on the first real deep tree.
///
/// `vendor_root` is the module the vendor directory corresponds to, e.g.
/// `Transformer.Vendor`; `vendor_dir` is where the files go.
pub fn plan(
    decls: &[Decl],
    imports: &[ModuleName],
    vendor_dir: &std::path::Path,
    vendor_root: &ModuleName,
    meta: &dyn Fn(&SourceId) -> Option<SourceMeta>,
) -> VendorPlan {
    let mut grouped: BTreeMap<(SourceId, ModuleName), Vec<Decl>> = BTreeMap::new();
    let mut by_source: BTreeMap<SourceId, usize> = BTreeMap::new();
    for d in decls {
        grouped.entry((d.source.clone(), d.module.clone())).or_default().push(d.clone());
        *by_source.entry(d.source.clone()).or_default() += 1;
    }

    let mut files = Vec::new();
    let mut project_imports = Vec::new();
    for ((source, origin), decls) in grouped {
        let module = vendored_module(vendor_root, &source, &origin);
        files.push(VendorFile {
            path: vendor_dir.join(vendored_relative_path(&source, &origin)),
            module: module.clone(),
            imports: imports.to_vec(),
            header: provenance_header(meta(&source).as_ref(), &source, &origin),
            decls,
        });
        project_imports.push(module);
    }
    project_imports.sort();
    VendorPlan { files, imports: project_imports, by_source }
}

/// `Transformer.Vendor` + source `flt` + `Thm.Foo` → `Transformer.Vendor.Flt.Thm.Foo`.
/// The source name is part of the path so two sources can carry the same module.
fn vendored_module(root: &ModuleName, source: &SourceId, origin: &ModuleName) -> ModuleName {
    ModuleName::new(format!("{root}.{}.{origin}", capitalize(source.as_str())))
}

fn vendored_relative_path(source: &SourceId, origin: &ModuleName) -> PathBuf {
    PathBuf::from(capitalize(source.as_str())).join(origin.relative_path())
}

fn capitalize(s: &str) -> String {
    let cleaned: String = s.chars().map(|c| if c.is_alphanumeric() { c } else { '_' }).collect();
    let mut chars = cleaned.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::decl::Span;
    use crate::domain::source::SourceKind;
    use std::path::Path;

    fn decl(name: &str, source: &str, module: &str, lines: (u32, u32)) -> Decl {
        let mut d = Decl::stub(name, source, module);
        d.span = Some(Span::new(lines.0, lines.1));
        d
    }

    fn meta(_: &SourceId) -> Option<SourceMeta> {
        let mut m = SourceMeta::derived("flt", SourceKind::Git);
        m.rev = Some("abc123".into());
        m.license = Some("Apache-2.0".into());
        m.attribution = Some("anthropics/fermats-last-theorem".into());
        Some(m)
    }

    #[test]
    fn declarations_from_one_module_land_in_one_file() {
        let decls = vec![
            decl("Thm.a", "flt", "Theorems.Thm_a", (1, 10)),
            decl("Thm.b", "flt", "Theorems.Thm_a", (12, 20)),
            decl("Thm.c", "flt", "Theorems.Thm_c", (1, 5)),
        ];
        let p = plan(
            &decls,
            &[ModuleName::new("Mathlib.Algebra.Basic")],
            Path::new("src/Transformer/Vendor"),
            &ModuleName::new("Transformer.Vendor"),
            &meta,
        );
        assert_eq!(p.files.len(), 2);
        assert_eq!(p.total_decls(), 3);
        assert_eq!(p.total_lines(), 10 + 9 + 5);
        assert_eq!(p.by_source.get(&SourceId::new("flt")), Some(&3));
    }

    #[test]
    fn the_vendored_module_is_reachable_and_namespaced_by_source() {
        let p = plan(
            &[decl("Thm.a", "flt", "Theorems.Thm_a", (1, 3))],
            &[],
            Path::new("src/Transformer/Vendor"),
            &ModuleName::new("Transformer.Vendor"),
            &meta,
        );
        assert_eq!(p.files[0].module.as_str(), "Transformer.Vendor.Flt.Theorems.Thm_a");
        assert_eq!(p.files[0].path, Path::new("src/Transformer/Vendor/Flt/Theorems/Thm_a.lean"));
        // The module has to be registered or it is not built.
        assert_eq!(p.imports, vec![ModuleName::new("Transformer.Vendor.Flt.Theorems.Thm_a")]);
    }

    #[test]
    fn the_header_names_source_path_revision_and_licence() {
        let h = provenance_header(
            meta(&SourceId::new("flt")).as_ref(),
            &SourceId::new("flt"),
            &ModuleName::new("Theorems.Thm_a"),
        );
        assert!(h.contains("Source:   flt"));
        assert!(h.contains("Theorems/Thm_a.lean"));
        assert!(h.contains("abc123"));
        assert!(h.contains("Apache-2.0"));
        assert!(h.contains("anthropics/fermats-last-theorem"));
        assert!(h.starts_with("/-") && h.ends_with("-/"));
    }

    #[test]
    fn an_empty_materialization_set_plans_nothing() {
        let p = plan(&[], &[], Path::new("v"), &ModuleName::new("V"), &meta);
        assert!(p.is_empty());
        assert_eq!(p.total_lines(), 0);
    }
}
