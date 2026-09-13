//! The composition root: the one place that knows which adapter implements
//! which port.
//!
//! Everything above this file is written against traits, so this is also the
//! only file that has to change to index something that is not a Lake project.

use crate::application::add::Add;
use crate::application::deps::Deps;
use crate::application::find::{Dup, Find};
use crate::application::index;
use crate::application::ports::{DeclRepo, DeclSink, FetchSpec, Workspace};
use crate::application::ship::Fetch;
use crate::application::show::Show;
use crate::application::status::Status;
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::pattern;
use crate::domain::query::Query;
use crate::domain::source::SourceId;
use crate::error::{Error, Result, bail};
use crate::infrastructure::config::{self, Config, Source};
use crate::infrastructure::git::Git;
use crate::infrastructure::jsonl::{self, JsonlRepo};
use crate::infrastructure::lake::{self, LakeElaborator};
use crate::infrastructure::project::{Files, Project};
use crate::infrastructure::sqlite::SqliteIndex;
use crate::interface::cli::{Cli, Command, FindArgs};
use crate::interface::render;
use std::collections::BTreeMap;
use std::path::PathBuf;

pub fn run(cli: Cli) -> Result<()> {
    // `init` is the one command that runs without a configuration, since its
    // whole job is to write one.
    if let Command::Init { force } = cli.command {
        return init(cli.config.as_deref(), force);
    }
    let cfg = Config::load(cli.config.as_deref())?;
    let app = App { workspace: cfg.workspace(), files: files(&cfg), verbose: cli.verbose, cfg };
    app.dispatch(cli.command)
}

struct App {
    cfg: Config,
    workspace: Workspace,
    files: Files,
    verbose: bool,
}

impl App {
    fn dispatch(&self, command: Command) -> Result<()> {
        match command {
            // Handled before the configuration is loaded.
            Command::Init { .. } => Ok(()),
            Command::Dump { source, no_deps } => self.dump(source.as_deref(), !no_deps),
            Command::Scan { source } => self.scan(source.as_deref()),
            Command::Fetch { source } => self.fetch(source.as_deref()),
            Command::Index { rebuild } => self.index(rebuild),
            Command::Status => self.status(),
            Command::Show { names, import_only } => self.show(&names, import_only),
            Command::Deps { name, depth } => self.deps(&name, &depth),
            Command::Add { name, write, force } => self.add(&name, write, force),
            Command::Find(args) => self.find(&args),
            Command::Dup { file, threshold } => self.dup(&file, threshold),
        }
    }

    // ---- reading ---------------------------------------------------------

    /// The index, or the raw dumps when there is no index yet. Falling back
    /// rather than failing means a dump is searchable before `dt index` has
    /// run, at the cost of holding it in memory.
    fn repo(&self) -> Result<Box<dyn DeclRepo>> {
        let db = self.cfg.db_path();
        if db.is_file() {
            return Ok(Box::new(SqliteIndex::open(&db)?));
        }
        let dumps: Vec<PathBuf> = self
            .cfg
            .sources
            .iter()
            .map(|s| self.cfg.jsonl_path(s))
            .filter(|p| p.is_file())
            .collect();
        if dumps.is_empty() {
            bail!("no index at {} and nothing dumped: run `dt dump` then `dt index`", db.display())
        }
        if self.verbose {
            eprintln!("dt: no index yet; reading {} dump(s) directly", dumps.len());
        }
        Ok(Box::new(JsonlRepo::open(&dumps)?))
    }

    /// A batch is not all-or-nothing. `dt show A B C` exists so an agent can pay
    /// for one round trip instead of three; failing the whole batch because one
    /// name was misremembered would hand back three round trips again. Misses go
    /// to stderr, so `--import-only` still redirects into a file cleanly, and an
    /// empty batch is still an error.
    fn show(&self, names: &[String], import_only: bool) -> Result<()> {
        let repo = self.repo()?;
        let show = Show { repo: repo.as_ref(), files: &self.files, workspace: &self.workspace };
        let mut shown = Vec::new();
        let mut missed = Vec::new();
        for n in names {
            match show.run(&DeclName::new(n.as_str())) {
                Ok(s) => shown.push(s),
                Err(e) => missed.push(e),
            }
        }
        if shown.is_empty() {
            return Err(missed.into_iter().next().expect("a batch has at least one name"));
        }
        print!("{}", render::show_all(&shown, import_only));
        for e in &missed {
            eprintln!("dt: {e}");
        }
        Ok(())
    }

    fn deps(&self, name: &str, depth: &str) -> Result<()> {
        let depth =
            match depth {
                "all" => None,
                d => Some(d.parse::<usize>().map_err(|_| {
                    Error::new(format!("--depth takes a number or `all`, not `{d}`"))
                })?),
            };
        let result = Deps { repo: self.repo()?.as_ref(), workspace: &self.workspace }
            .run(&DeclName::new(name), depth)?;
        print!("{}", render::deps(&result));
        Ok(())
    }

    fn find(&self, args: &FindArgs) -> Result<()> {
        let query = query_of(args)?;
        if self.verbose {
            if let Some(p) = &args.pattern {
                let parsed = pattern::parse(p);
                eprintln!(
                    "dt: `{p}` read as conclusion {}, {} argument(s){}",
                    parsed.query.shape.concl.as_ref().map_or("_", |c| c.as_str()),
                    parsed.query.shape.args.len(),
                    parsed.operator.map_or(String::new(), |o| format!(", operator `{o}`")),
                );
            }
        }
        let hits = Find { repo: self.repo()?.as_ref() }.run(&query)?;
        print!("{}", render::find(&hits, args.long));
        Ok(())
    }

    fn status(&self) -> Result<()> {
        let rows = Status { repo: self.repo()?.as_ref(), workspace: &self.workspace }.run()?;
        print!("{}", render::status(&rows, &self.cfg.db_path()));
        Ok(())
    }

    fn dup(&self, file: &std::path::Path, threshold: f32) -> Result<()> {
        let local = self
            .cfg
            .sources
            .iter()
            .find(|s| s.kind == config::Kind::Local)
            .map(|s| SourceId::new(s.name.clone()))
            .unwrap_or_else(|| SourceId::new("project"));
        let module = self.module_of(file);
        let dups = Dup { repo: self.repo()?.as_ref(), files: &self.files, local, threshold }
            .run(file, &module)?;
        print!("{}", render::dup(&dups));
        Ok(())
    }

    /// What a path under `src` is called once built.
    fn module_of(&self, file: &std::path::Path) -> ModuleName {
        let abs = if file.is_absolute() {
            file.to_path_buf()
        } else {
            std::env::current_dir().unwrap_or_default().join(file)
        };
        abs.strip_prefix(self.cfg.resolve(&self.cfg.project.src))
            .ok()
            .and_then(ModuleName::from_relative_path)
            .unwrap_or_else(|| ModuleName::new(self.cfg.project.namespace.clone()))
    }

    // ---- writing ---------------------------------------------------------

    fn add(&self, name: &str, write: bool, force: bool) -> Result<()> {
        let repo = self.repo()?;
        let add = Add { repo: repo.as_ref(), files: &self.files, workspace: &self.workspace };
        let name = DeclName::new(name);
        let report = if write {
            let mut project = Project { imports_file: self.cfg.imports_file() };
            add.write(&name, &mut project, force)?
        } else {
            add.plan(&name)?
        };
        print!("{}", render::add(&report, write));
        Ok(())
    }

    // ---- building the index ---------------------------------------------

    fn dump(&self, source: Option<&str>, with_deps: bool) -> Result<()> {
        let root = self.cfg.root();
        if !lake::is_lake_project(&root) {
            bail!(
                "{} is not a Lake project, so there is nothing to elaborate; \
                 set `project.root` in {}",
                root.display(),
                config::FILE_NAME
            )
        }
        let lean = LakeElaborator {
            project_root: root,
            work_dir: self.cfg.raw_dir().join("scripts"),
            verbose: self.verbose,
        };
        for s in self.select(source, |s| s.elaborated())? {
            let Some(root_module) = &s.root else { continue };
            let out = self.cfg.jsonl_path(s);
            let path = index::dump_source(
                &s.meta(),
                root_module,
                &s.module_prefixes(),
                out,
                with_deps,
                &lean,
            )?;
            println!("{}: dumped to {}", s.name, path.display());
        }
        Ok(())
    }

    fn scan(&self, source: Option<&str>) -> Result<()> {
        // Text rows are scanned straight into the index, because the scanner
        // needs the already-indexed corpus to tell a real constant from a
        // bound variable.
        let mut db = SqliteIndex::open(&self.cfg.db_path())?;
        for s in self.select(source, |s| !s.elaborated())? {
            let scan = index::scan_source(&s.meta(), &self.files, Some(&db))?;
            db.clear_source(&SourceId::new(s.name.clone()))?;
            index::load(&mut db, &scan.decls)?;
            println!(
                "{}: {} declarations scanned [text]{}",
                s.name,
                scan.decls.len(),
                anonymous_note(scan.anonymous)
            );
        }
        db.finish()?;
        Ok(())
    }

    fn fetch(&self, source: Option<&str>) -> Result<()> {
        let git = Git { verbose: self.verbose };
        let fetch = Fetch { vcs: &git };
        for s in self.select(source, |s| s.kind == config::Kind::Git)? {
            let Some(url) = &s.url else {
                println!("{}: has a local path, nothing to fetch", s.name);
                continue;
            };
            let fetched = fetch.run(&FetchSpec {
                source: SourceId::new(s.name.clone()),
                url: url.clone(),
                rev: s.rev.clone().unwrap_or_else(|| "main".into()),
                sparse: s.sparse.clone(),
                into: self.cfg.source_dir(s),
            })?;
            println!(
                "{}: {} at {}",
                s.name,
                fetched.path.display(),
                fetched.revision.as_deref().unwrap_or("unknown revision")
            );
        }
        Ok(())
    }

    fn index(&self, rebuild: bool) -> Result<()> {
        let db = self.cfg.db_path();
        if rebuild && db.exists() {
            std::fs::remove_file(&db)?;
        }
        if let Some(parent) = db.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut sqlite = SqliteIndex::open(&db)?;

        // Compiled sources first: the text scanner resolves its identifiers
        // against what is already indexed, so an empty index would leave every
        // text row with no dependencies at all.
        for s in self.cfg.sources.iter().filter(|s| s.elaborated()) {
            let path = self.cfg.jsonl_path(s);
            if !path.is_file() {
                eprintln!("{}: not dumped yet, skipping (`dt dump {}`)", s.name, s.name);
                continue;
            }
            let decls = jsonl::read_parallel(&path)?;
            let id = SourceId::new(s.name.clone());
            sqlite.clear_source(&id)?;
            index::load(&mut sqlite, &decls)?;
            report(&s.name, decls.len(), sqlite.count_source(&id)?, "");
        }
        for s in self.cfg.sources.iter().filter(|s| !s.elaborated()) {
            let dir = self.cfg.source_dir(s);
            if !dir.is_dir() {
                eprintln!("{}: not on disk yet, skipping (`dt fetch {}`)", s.name, s.name);
                continue;
            }
            let scan = index::scan_source(&s.meta(), &self.files, Some(&sqlite))?;
            let id = SourceId::new(s.name.clone());
            sqlite.clear_source(&id)?;
            index::load(&mut sqlite, &scan.decls)?;
            let tag = format!(" [text]{}", anonymous_note(scan.anonymous));
            report(&s.name, scan.decls.len(), sqlite.count_source(&id)?, &tag);
        }
        sqlite.finish()?;
        println!("\nindex: {} ({} rows)", db.display(), sqlite.count()?);
        Ok(())
    }

    /// The sources a command applies to: the one named, or every source the
    /// command makes sense for.
    fn select(
        &self,
        name: Option<&str>,
        applies: impl Fn(&Source) -> bool,
    ) -> Result<Vec<&Source>> {
        match name {
            Some(n) => {
                let s = self.cfg.source(n)?;
                if !applies(s) {
                    bail!("source `{}` is not of the right kind for this command", s.name)
                }
                Ok(vec![s])
            }
            None => {
                let v: Vec<&Source> = self.cfg.sources.iter().filter(|s| applies(s)).collect();
                if v.is_empty() {
                    bail!("no source in {} applies to this command", config::FILE_NAME)
                }
                Ok(v)
            }
        }
    }
}

fn init(explicit: Option<&std::path::Path>, force: bool) -> Result<()> {
    let path = explicit
        .map(std::path::Path::to_path_buf)
        .unwrap_or_else(|| PathBuf::from(config::FILE_NAME));
    if path.exists() && !force {
        bail!("{} already exists; re-run with --force to replace it", path.display())
    }
    std::fs::write(&path, config::TEMPLATE)?;
    println!(
        "wrote {}\n\nNext: `dt dump` to read the Lean environment, then `dt index`.",
        path.display()
    );
    Ok(())
}

fn files(cfg: &Config) -> Files {
    let mut roots = BTreeMap::new();
    let mut excludes = BTreeMap::new();
    for s in &cfg.sources {
        let id = SourceId::new(s.name.clone());
        roots.insert(id.clone(), cfg.source_dir(s));
        if !s.exclude.is_empty() {
            excludes.insert(id, s.exclude.clone());
        }
    }
    Files { roots, excludes }
}

/// The command line as a domain query. A pattern supplies the shape; the
/// explicit flags refine it, and win where both say something.
fn query_of(a: &FindArgs) -> Result<Query> {
    let mut q = match &a.pattern {
        Some(p) => pattern::parse(p).query,
        None => Query::new(),
    };
    if a.name.is_some() {
        q.name = a.name.clone();
    }
    if let Some(c) = &a.concl {
        q.shape.concl = Some(DeclName::new(c.clone()));
    }
    q.uses.extend(a.uses.iter().map(DeclName::new));
    if a.module.is_some() {
        q.module = a.module.clone();
    }
    q.source = a.source.as_ref().map(SourceId::new);
    if let Some(k) = &a.kind {
        q.kind = Some(crate::domain::decl::DeclKind::parse(k));
    }
    if a.text.is_some() {
        q.text = a.text.clone();
    }
    // Asking for a shape means asking a question a text row cannot answer, so
    // the flag is implied rather than silently ignored.
    q.elaborated_only = a.elaborated || q.needs_shape();
    q.no_sorry = a.no_sorry;
    q.limit = a.limit;
    Ok(q)
}

/// What was left out for having no name, said once rather than per file.
fn anonymous_note(n: usize) -> String {
    if n == 0 { String::new() } else { format!(", {n} anonymous") }
}

/// What a source contributed, and what became of it. `handed` and `stored`
/// differ when two declarations share a (name, source, module) identity, so
/// printing only one of the two numbers hides a corpus losing rows.
fn report(name: &str, handed: usize, stored: usize, tag: &str) {
    if handed == stored {
        println!("{name}: {stored} declarations indexed{tag}");
    } else {
        println!(
            "{name}: {stored} declarations indexed{tag} ({} lost to a name \
             already taken in the same module)",
            handed - stored
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::Parser;

    fn args(argv: &[&str]) -> FindArgs {
        match Cli::parse_from(argv).command {
            Command::Find(a) => a,
            _ => unreachable!("not a find"),
        }
    }

    #[test]
    fn a_pattern_becomes_a_shape_query() {
        let q = query_of(&args(&["dt", "find", "Real.exp _ ≤ _"])).unwrap();
        assert_eq!(q.shape.concl.as_ref().map(|c| c.as_str()), Some("LE.le"));
        assert_eq!(q.shape.args.len(), 2);
    }

    #[test]
    fn asking_for_a_shape_restricts_the_search_to_elaborated_rows() {
        // Not a convenience: a text row has no conclusion head symbol, so
        // including one would drop the condition instead of failing it.
        assert!(query_of(&args(&["dt", "find", "Real.exp _ ≤ _"])).unwrap().elaborated_only);
        assert!(!query_of(&args(&["dt", "find", "--name", "exp"])).unwrap().elaborated_only);
    }

    #[test]
    fn explicit_flags_refine_a_pattern() {
        let q = query_of(&args(&[
            "dt",
            "find",
            "_ ≤ _",
            "--in",
            "Mathlib.Analysis",
            "--uses",
            "Real.exp,Real.log",
            "--limit",
            "5",
        ]))
        .unwrap();
        assert_eq!(q.module.as_deref(), Some("Mathlib.Analysis"));
        assert_eq!(q.uses.len(), 2);
        assert_eq!(q.limit, 5);
    }

    #[test]
    fn a_query_with_no_conditions_is_recognised_as_empty() {
        assert!(query_of(&args(&["dt", "find"])).unwrap().is_empty());
    }
}
