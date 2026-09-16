//! The wire format between `lean/dump.lean` and the rest of the tool, and a
//! repository that reads it directly.
//!
//! The DTO lives here rather than on the entity so that the JSON the Lean file
//! happens to emit is not part of the domain. Changing the dump changes this
//! file and nothing else.

use crate::application::ports::{DeclRepo, Mention};
use crate::domain::decl::{self, ArgHead, Decl, DeclKind, Shape, Span};
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::query::Query;
use crate::domain::source::SourceId;
use crate::error::{Error, Result};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};

#[derive(Debug, Serialize, Deserialize)]
pub struct Row {
    pub name: String,
    pub source: String,
    pub module: String,
    pub kind: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub concl: Option<String>,
    #[serde(default)]
    pub concl_args: Vec<String>,
    #[serde(default)]
    pub consts: Vec<String>,
    #[serde(default)]
    pub deps: Vec<String>,
    #[serde(default)]
    pub doc: Option<String>,
    #[serde(rename = "sorry", default)]
    pub has_sorry: bool,
    #[serde(default)]
    pub line_start: Option<u32>,
    #[serde(default)]
    pub line_end: Option<u32>,
    pub elaborated: bool,
}

impl From<Row> for Decl {
    fn from(r: Row) -> Decl {
        Decl {
            name: DeclName::new(r.name),
            source: SourceId::new(r.source),
            module: ModuleName::new(r.module),
            kind: DeclKind::parse(&r.kind),
            ty: r.ty,
            shape: Shape::new(
                r.concl.map(DeclName::new),
                r.concl_args.iter().map(|a| ArgHead::parse(a)).collect(),
            ),
            consts: r.consts.into_iter().map(DeclName::new).collect(),
            deps: r.deps.into_iter().map(DeclName::new).collect(),
            doc: r.doc,
            has_sorry: r.has_sorry,
            span: match (r.line_start, r.line_end) {
                (Some(a), Some(b)) => Some(Span::new(a, b)),
                _ => None,
            },
            elaborated: r.elaborated,
        }
    }
}

impl From<&Decl> for Row {
    fn from(d: &Decl) -> Row {
        Row {
            name: d.name.to_string(),
            source: d.source.to_string(),
            module: d.module.to_string(),
            kind: d.kind.to_string(),
            ty: d.ty.clone(),
            concl: d.shape.concl.as_ref().map(DeclName::to_string),
            concl_args: d.shape.args.iter().map(|a| a.as_str().to_string()).collect(),
            consts: d.consts.iter().map(DeclName::to_string).collect(),
            deps: d.deps.iter().map(DeclName::to_string).collect(),
            doc: d.doc.clone(),
            has_sorry: d.has_sorry,
            line_start: d.span.map(|s| s.start),
            line_end: d.span.map(|s| s.end),
            elaborated: d.elaborated,
        }
    }
}

/// Read a dump. Lines that will not parse are skipped rather than fatal: a
/// single malformed row out of half a million must not lose the dump.
pub fn read(path: &Path) -> Result<Vec<Decl>> {
    let file =
        std::fs::File::open(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    let mut out = Vec::new();
    for line in BufReader::with_capacity(1 << 20, file).lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        if let Ok(row) = serde_json::from_str::<Row>(&line) {
            out.push(row.into());
        }
    }
    Ok(out)
}

/// Read a dump in bounded memory, handing each batch of rows to `sink` as soon
/// as it is parsed.
///
/// [`read_parallel`] is the obvious way to do this and it costs four times the
/// file: the whole text is resident while the whole `Vec<Decl>` is being built
/// beside it, and the rows are the larger half. A 231 MB Mathlib dump peaked at
/// 936 MB that way, and it scales with the corpus — the reason to index a
/// library is that it is large.
///
/// The read stays serial and buffered; only the parse is spread over the cores,
/// a batch at a time. Reading 231 MB off a warm page cache is not the cost here,
/// parsing it is.
pub fn stream(path: &Path, mut sink: impl FnMut(&[Decl]) -> Result<()>) -> Result<usize> {
    /// Lines held at once. Large enough that the fork-and-join is amortised,
    /// small enough that the batch is megabytes rather than hundreds of them.
    const BATCH: usize = 8192;

    let file =
        std::fs::File::open(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    let mut lines = BufReader::with_capacity(1 << 20, file).lines();
    let mut raw: Vec<String> = Vec::with_capacity(BATCH);
    let mut total = 0;
    loop {
        raw.clear();
        for line in lines.by_ref().take(BATCH) {
            raw.push(line?);
        }
        if raw.is_empty() {
            return Ok(total);
        }
        let decls: Vec<Decl> = raw
            .par_iter()
            .filter(|l| !l.trim().is_empty())
            .filter_map(|l| serde_json::from_str::<Row>(l).ok())
            .map(Decl::from)
            .collect();
        total += decls.len();
        sink(&decls)?;
    }
}

/// Read a dump in parallel, all of it at once. Used where the rows are wanted
/// as a collection anyway — `JsonlRepo`, which is a repository over the dumps
/// themselves. Prefer [`stream`] when the rows are only being passed through.
pub fn read_parallel(path: &Path) -> Result<Vec<Decl>> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    Ok(text
        .par_lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| serde_json::from_str::<Row>(l).ok())
        .map(Decl::from)
        .collect())
}

pub fn write(path: &Path, decls: &[Decl]) -> Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let file =
        std::fs::File::create(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    let mut w = BufWriter::with_capacity(1 << 20, file);
    for d in decls {
        serde_json::to_writer(&mut w, &Row::from(d))?;
        w.write_all(b"\n")?;
    }
    w.flush()?;
    Ok(())
}

/// A repository backed by the raw dumps, so `dt show` and `dt deps` work
/// immediately after a dump, before any index has been built.
pub struct JsonlRepo {
    decls: Vec<Decl>,
}

impl JsonlRepo {
    pub fn open(paths: &[PathBuf]) -> Result<JsonlRepo> {
        let mut decls = Vec::new();
        for p in paths {
            if p.exists() {
                decls.extend(read_parallel(p)?);
            }
        }
        Ok(JsonlRepo { decls })
    }

    pub fn from_decls(decls: Vec<Decl>) -> JsonlRepo {
        JsonlRepo { decls }
    }

    pub fn len(&self) -> usize {
        self.decls.len()
    }

    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }
}

impl DeclRepo for JsonlRepo {
    fn named(&self, name: &DeclName) -> Result<Vec<Decl>> {
        let mut rows: Vec<Decl> = self.decls.iter().filter(|d| &d.name == name).cloned().collect();
        rows.sort_by_key(|d| !d.elaborated);
        Ok(rows)
    }

    fn find(&self, query: &Query) -> Result<Vec<Decl>> {
        Ok(self.decls.par_iter().filter(|d| query.matches(d)).cloned().collect())
    }

    fn get_many(&self, names: &[DeclName]) -> Result<Vec<Decl>> {
        let wanted: std::collections::HashSet<&DeclName> = names.iter().collect();
        let mut found: Vec<Decl> =
            self.decls.iter().filter(|d| wanted.contains(&d.name)).cloned().collect();
        // Preserve the order asked for: `dt add` depends on it being
        // topological.
        let position: std::collections::HashMap<&DeclName, usize> =
            names.iter().enumerate().map(|(i, n)| (n, i)).collect();
        found.sort_by_key(|d| position.get(&d.name).copied().unwrap_or(usize::MAX));
        Ok(found)
    }

    fn used_by(&self, name: &DeclName, within: &Query) -> Result<Vec<Mention>> {
        Ok(self.decls.iter().filter_map(|d| Mention::of(d, name, within)).collect())
    }

    fn ending_in(&self, field: &DeclName) -> Result<Vec<DeclName>> {
        let names: std::collections::BTreeSet<&DeclName> =
            self.decls.iter().map(|d| &d.name).filter(|n| field.names(n)).collect();
        let mut names: Vec<DeclName> = names.into_iter().cloned().collect();
        // Stable, so a tie stays in name order.
        names.sort_by_key(|n| {
            std::cmp::Reverse(self.decls.iter().filter(|d| d.consts.contains(n)).count())
        });
        Ok(names)
    }

    fn heads_called(&self, word: &str) -> Result<Vec<DeclName>> {
        Ok(decl::commonest_called(
            self.decls.iter().map(|d| (d.ty.as_str(), d.shape.heads().collect())),
            word,
        ))
    }

    fn counts(&self) -> Result<Vec<(SourceId, usize)>> {
        let mut m: std::collections::BTreeMap<SourceId, usize> = Default::default();
        for d in &self.decls {
            *m.entry(d.source.clone()).or_default() += 1;
        }
        Ok(m.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decl() -> Decl {
        let mut d =
            Decl::stub("Real.exp_le_exp", "mathlib", "Mathlib.Analysis.Complex.Exponential");
        d.ty = "Real.exp x ≤ Real.exp y ↔ x ≤ y".into();
        d.shape = Shape::new(
            Some(DeclName::new("Iff")),
            vec![ArgHead::parse("LE.le"), ArgHead::parse("_")],
        );
        d.consts = vec![DeclName::new("Real.exp"), DeclName::new("LE.le")];
        d.deps = vec![DeclName::new("Real.add_pow_le_pow_mul_pow_of_sq_le_sq")];
        d.doc = Some("`exp` is monotone.".into());
        d.span = Some(Span::new(316, 318));
        d
    }

    #[test]
    fn a_row_survives_a_round_trip() {
        let d = decl();
        let json = serde_json::to_string(&Row::from(&d)).unwrap();
        let back: Decl = serde_json::from_str::<Row>(&json).unwrap().into();
        assert_eq!(back, d);
    }

    #[test]
    fn the_json_the_lean_dump_writes_deserialises() {
        // Copied from an actual `lean/dump.lean` line, field order and all.
        let line = r#"{"concl":"List","concl_args":["Sigma"],"consts":["List","Sigma"],"deps":["List.map"],"doc":"docs","elaborated":true,"kind":"def","line_end":528,"line_start":523,"module":"Batteries.Data.List.Basic","name":"List.sigma","sorry":false,"source":"mathlib","type":"List a"}"#;
        let d: Decl = serde_json::from_str::<Row>(line).unwrap().into();
        assert_eq!(d.name.as_str(), "List.sigma");
        assert_eq!(d.kind, DeclKind::Def);
        assert_eq!(d.span, Some(Span::new(523, 528)));
        assert_eq!(d.shape.concl, Some(DeclName::new("List")));
        assert!(d.elaborated);
    }

    #[test]
    fn a_null_conclusion_and_range_are_accepted() {
        let line = r#"{"concl":null,"concl_args":[],"consts":[],"deps":[],"doc":null,"elaborated":false,"kind":"theorem","line_end":null,"line_start":null,"module":"M","name":"n","sorry":true,"source":"flt","type":"t"}"#;
        let d: Decl = serde_json::from_str::<Row>(line).unwrap().into();
        assert_eq!(d.span, None);
        assert!(!d.shaped());
        assert!(d.has_sorry);
    }

    #[test]
    fn a_malformed_line_does_not_lose_the_dump() {
        let dir = tempdir();
        let path = dir.join("x.jsonl");
        let good = serde_json::to_string(&Row::from(&decl())).unwrap();
        std::fs::write(&path, format!("{good}\nnot json at all\n\n{good}\n")).unwrap();
        assert_eq!(read(&path).unwrap().len(), 2);
        assert_eq!(read_parallel(&path).unwrap().len(), 2);

        let mut seen = 0;
        assert_eq!(
            stream(&path, |c| {
                seen += c.len();
                Ok(())
            })
            .unwrap(),
            2
        );
        assert_eq!(seen, 2, "the streaming reader must skip the same rows");
    }

    /// The batch boundary is the part that can silently lose rows: an off-by-one
    /// in the take-N loop drops the last partial batch, and every dump has one.
    #[test]
    fn streaming_crosses_batch_boundaries_without_losing_rows() {
        let path = tempdir().join("batched.jsonl");
        let rows: Vec<String> = (0..20_000)
            .map(|i| {
                serde_json::to_string(&Row::from(&Decl::stub(&format!("d{i}"), "s", "M"))).unwrap()
            })
            .collect();
        std::fs::write(&path, rows.join("\n")).unwrap();

        let mut names = Vec::new();
        let total = stream(&path, |c| {
            names.extend(c.iter().map(|d| d.name.to_string()));
            Ok(())
        })
        .unwrap();
        assert_eq!(total, 20_000);
        assert_eq!(names.len(), 20_000);
        // Order is what `dt add` depends on, and a parallel parse is where it
        // would be lost.
        assert_eq!(names[0], "d0");
        assert_eq!(names[19_999], "d19999");
    }

    #[test]
    fn the_repo_preserves_the_order_of_get_many() {
        let repo = JsonlRepo::from_decls(vec![
            Decl::stub("c", "s", "M"),
            Decl::stub("a", "s", "M"),
            Decl::stub("b", "s", "M"),
        ]);
        let asked = vec![DeclName::new("b"), DeclName::new("c"), DeclName::new("a")];
        let got: Vec<String> =
            repo.get_many(&asked).unwrap().iter().map(|d| d.name.to_string()).collect();
        assert_eq!(got, vec!["b", "c", "a"], "dt add depends on topological order surviving");
    }

    fn tempdir() -> PathBuf {
        let p = std::env::temp_dir().join(format!("discrtree-test-{}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        p
    }
}
