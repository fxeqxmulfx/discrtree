//! The composition root: the one place that knows which adapter implements
//! which port.
//!
//! Everything above this file is written against traits, so this is also the
//! only file that has to change to index something that is not a Lake project.

use crate::application::add::Add;
use crate::application::deps::{Deps, DepsResult};
use crate::application::find::{Dup, Find};
use crate::application::index;
use crate::application::ports::{DeclRepo, DeclSink, FetchSpec, Provenance, Revisions, Workspace};
use crate::application::ship::Fetch;
use crate::application::show::Show;
use crate::application::status::{self, Status};
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::pattern;
use crate::domain::query::Query;
use crate::domain::source::SourceId;
use crate::error::{Error, Result, bail};
use crate::infrastructure::config::{self, Config, Source};
use crate::infrastructure::git::Git;
use crate::infrastructure::jsonl::{self, JsonlRepo};
use crate::infrastructure::lake::{self, LakeBuild, LakeElaborator};
use crate::infrastructure::project::{Files, Project};
use crate::infrastructure::revision::{self, OnDisk};
use crate::infrastructure::sqlite::SqliteIndex;
use crate::interface::cli::{Cli, Command, FindArgs};
use crate::interface::render;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

pub fn run(cli: Cli) -> Result<()> {
    // `init` is the one command that runs without a configuration, since its
    // whole job is to write one.
    match cli.command {
        Command::Init { force } => return init(cli.config.as_deref(), force),
        Command::Skill { install } => return skill(install),
        _ => {}
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
            Command::Init { .. } | Command::Skill { .. } => Ok(()),
            Command::Dump { source, source_flag, no_deps } => {
                self.dump(named(source, source_flag).as_deref(), !no_deps)
            }
            Command::Scan { source, source_flag } => {
                self.scan(named(source, source_flag).as_deref())
            }
            Command::Fetch { source, source_flag } => {
                self.fetch(named(source, source_flag).as_deref())
            }
            Command::Index { source, source_flag, rebuild, force } => {
                let only = self.only(named(source, source_flag).as_deref())?;
                self.index(only.as_deref(), rebuild, force)
            }
            Command::Refresh { source, source_flag } => {
                self.refresh(named(source, source_flag).as_deref())
            }
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

    /// Two ways to ask for something that cannot exist, both worth refusing
    /// before the search rather than answering `no match` afterwards. A source
    /// name is a closed set, so a wrong one can be corrected in the error
    /// instead of merely reported. And a shape cannot be asked of a text
    /// source at all: a scanned row has no conclusion head symbol, so that
    /// search is not empty, it is unanswerable — and the two look identical
    /// from outside.
    fn check_source(&self, query: &Query) -> Result<()> {
        let Some(s) = &query.source else { return Ok(()) };
        if self.workspace.sources.get(s).is_none() {
            let known: Vec<&str> = self.workspace.sources.iter().map(|m| m.id.as_str()).collect();
            bail!("no source `{s}`; configured sources are {}", known.join(", "))
        }
        if query.needs_shape() && !self.workspace.sources.elaborated(s) {
            bail!(
                "source `{s}` is text, and a shape can only be matched against elaborated rows; \
                 search it by --name, --text, --in or --uses instead"
            )
        }
        Ok(())
    }

    /// A batch is not all-or-nothing. `dt show A B C` exists so an agent can pay
    /// for one round trip instead of three; failing the whole batch because one
    /// name was misremembered would hand back three round trips again. Misses go
    /// to stderr, so `--import-only` still redirects into a file cleanly, and an
    /// empty batch is still an error.
    fn show(&self, names: &[String], import_only: bool) -> Result<()> {
        let repo = self.repo()?;
        let build = LakeBuild::read(&self.cfg);
        let show = Show {
            repo: repo.as_ref(),
            files: &self.files,
            workspace: &self.workspace,
            build: &build,
        };
        let mut shown = Vec::new();
        let mut missed = Vec::new();
        for n in names {
            match show.run(&DeclName::new(n.as_str())) {
                Ok(s) => shown.push(s),
                Err(e) => missed.push(e),
            }
        }
        if shown.is_empty() {
            // Every name missed, which is the case the warning is for: check
            // every source before handing back "not in the index".
            self.warn_stale(repo.as_ref(), BTreeSet::new());
            return Err(missed.into_iter().next().expect("a batch has at least one name"));
        }
        print!("{}", render::show_all(&shown, import_only));
        for e in &missed {
            eprintln!("dt: {e}");
        }
        let from = match missed.is_empty() {
            true => shown.iter().map(|s| s.decl.source.clone()).collect(),
            false => BTreeSet::new(),
        };
        self.warn_stale(repo.as_ref(), from);
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
        let repo = self.repo()?;
        // Not `?`: a declaration the index has not heard of is exactly what a
        // stale source hides, and the root is the one row whose absence ends
        // the command. So the warning is reached on both paths.
        let build = LakeBuild::read(&self.cfg);
        let deps = Deps { repo: repo.as_ref(), workspace: &self.workspace, build: &build };
        match deps.run(&DeclName::new(name), depth) {
            Ok(result) => {
                print!("{}", render::deps(&result));
                self.warn_stale(repo.as_ref(), closure_sources(&result));
                Ok(())
            }
            Err(e) => {
                self.warn_stale(repo.as_ref(), BTreeSet::new());
                Err(e)
            }
        }
    }

    fn find(&self, args: &FindArgs) -> Result<()> {
        let query = query_of(args)?;
        self.check_source(&query)?;
        let parsed = args.pattern.as_deref().map(pattern::parse);
        if let Some(p) = &parsed
            && !p.unknown.is_empty()
        {
            // Before the search rather than after it, because the search
            // would succeed: what it would return is the pattern minus the
            // part that made it this pattern.
            print!("{}", render::unreadable(&p.unknown));
            return Ok(());
        }
        if self.verbose {
            if let Some((p, parsed)) = args.pattern.as_deref().zip(parsed) {
                eprintln!(
                    "dt: `{p}` read as conclusion {}, {} argument(s){}{}{}",
                    parsed.query.shape.concl.as_ref().map_or("_", |c| c.as_str()),
                    parsed.query.shape.args.len(),
                    parsed.operator.map_or(String::new(), |o| format!(", operator `{o}`")),
                    match parsed.variables.is_empty() {
                        true => String::new(),
                        false => format!(", `{}` as `_`", parsed.variables.join("`, `")),
                    },
                    match parsed.hypotheses {
                        0 => String::new(),
                        n => format!(", {n} hypothesis/es as --uses"),
                    },
                );
            }
        }
        let repo = self.repo()?;
        let build = LakeBuild::read(&self.cfg);
        let hits = Find { repo: repo.as_ref(), build: &build }.run(&query)?;
        // On stderr, and before the rows: the answer below is to a question
        // spelled differently from the one that was asked, and a reader who
        // is piping the rows somewhere should still be told.
        for (written, read) in &hits.read_as {
            eprintln!("dt: `{written}` read as `{read}`");
        }
        print!("{}", render::find(&hits, args.long));
        self.warn_stale(repo.as_ref(), hits.rows.iter().map(|d| d.source.clone()).collect());
        Ok(())
    }

    /// One line on stderr when a source a search touched has changed since it
    /// was indexed.
    ///
    /// `dt status` reports this already, and nobody runs `dt status` before a
    /// search. What a stale index gives back is not a poor answer but a
    /// confident wrong one, and `no match` is the worst of them: it reads as
    /// "upstream has no such lemma, write it yourself" when the lemma was in
    /// the project all along, compiled after the last dump.
    ///
    /// An empty `from` means every source, not none. That is deliberate — a
    /// result with no rows names no sources, and it is exactly the result the
    /// warning exists for. It is also the one where checking costs nothing,
    /// because there were no rows to read in the first place.
    fn warn_stale(&self, repo: &dyn DeclRepo, from: BTreeSet<SourceId>) {
        let among: Vec<SourceId> = match from.is_empty() {
            true => self.workspace.sources.iter().map(|s| s.id.clone()).collect(),
            false => from.into_iter().collect(),
        };
        let revs = OnDisk::read(&self.cfg);
        // A search that failed because its warning failed would be a worse
        // outcome than the staleness the warning was about to report.
        let Ok(stale) = status::stale_among(repo, &revs, among) else { return };
        for s in stale {
            let kind = self.workspace.sources.iter().find(|w| w.id == s.id).map(|w| w.kind);
            eprint!("{}", render::stale(&s, kind));
        }
    }

    fn status(&self) -> Result<()> {
        let revs = OnDisk::read(&self.cfg);
        let report = Status {
            repo: self.repo()?.as_ref(),
            revisions: &revs,
            build: &LakeBuild::read(&self.cfg),
            workspace: &self.workspace,
            now: now(),
        }
        .run()?;
        print!("{}", render::status(&report, &self.cfg.db_path()));
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
            let Some(root_module) = s.root_module() else { continue };
            let out = self.cfg.jsonl_path(s);
            let path = index::dump_source(
                &s.meta(),
                &root_module,
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
        let revs = OnDisk::read(&self.cfg);
        for s in self.select(source, |s| !s.elaborated())? {
            let scan = index::scan_source(&s.meta(), &self.files, Some(&db))?;
            let id = SourceId::new(s.name.clone());
            db.clear_source(&id)?;
            index::load(&mut db, &scan.decls)?;
            // `dt scan` was asked for, so it is not skipped — but it still has
            // to leave the provenance behind, or the next `dt index` would
            // redo the work it just did.
            let revision = revs.current(&id)?;
            let decls = db.count_source(&id)?;
            db.record(
                &id,
                &Provenance {
                    stamp: revision.clone(),
                    revision,
                    indexed_at: now(),
                    decls,
                    ..Provenance::by_this_build()
                },
            )?;
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

    /// The sources `dt index` was pointed at, as names it has already checked
    /// exist. `None` is every source, which is what indexing has always meant.
    fn only(&self, source: Option<&str>) -> Result<Option<Vec<String>>> {
        match source {
            Some(n) => Ok(Some(vec![self.cfg.source(n)?.name.clone()])),
            None => Ok(None),
        }
    }

    fn index(&self, only: Option<&[String]>, rebuild: bool, force: bool) -> Result<()> {
        let wanted = |s: &Source| only.is_none_or(|only| only.contains(&s.name));
        let db = self.cfg.db_path();
        if rebuild && db.exists() {
            std::fs::remove_file(&db)?;
        }
        if let Some(parent) = db.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let mut sqlite = SqliteIndex::open(&db)?;
        let revs = OnDisk::read(&self.cfg);
        let mut changed = false;

        // Compiled sources first: the text scanner resolves its identifiers
        // against what is already indexed, so an empty index would leave every
        // text row with no dependencies at all.
        for s in self.cfg.sources.iter().filter(|s| s.elaborated() && wanted(s)) {
            let path = self.cfg.jsonl_path(s);
            if !path.is_file() {
                eprintln!("{}: not dumped yet, skipping (`dt dump {}`)", s.name, s.name);
                continue;
            }
            let id = SourceId::new(s.name.clone());
            // The input to indexing a compiled source is the dump, not the
            // library: a Mathlib bump that has not been dumped again changes
            // nothing here, and re-reading 700 MB to discover that is the work
            // this avoids.
            let was = Provenance {
                revision: revs.current(&id)?,
                stamp: revision::file_stamp(&path),
                indexed_at: now(),
                decls: 0,
                ..Provenance::by_this_build()
            };
            if self.up_to_date(&sqlite, &id, &was, force)? {
                continue;
            }
            sqlite.clear_source(&id)?;
            let read = jsonl::stream(&path, |chunk| sqlite.put(chunk))?;
            let stored = sqlite.count_source(&id)?;
            sqlite.record(&id, &Provenance { decls: stored, ..was })?;
            changed = true;
            report(&s.name, read, stored, "");
        }
        for s in self.cfg.sources.iter().filter(|s| !s.elaborated() && wanted(s)) {
            let dir = self.cfg.source_dir(s);
            if !dir.is_dir() {
                eprintln!("{}: not on disk yet, skipping (`dt fetch {}`)", s.name, s.name);
                continue;
            }
            let id = SourceId::new(s.name.clone());
            // A text source is read from the checkout, so its revision is also
            // its fingerprint. A directory that is not a checkout has neither,
            // and is read again every time.
            let revision = revs.current(&id)?;
            let was = Provenance {
                stamp: revision.clone(),
                revision,
                indexed_at: now(),
                decls: 0,
                ..Provenance::by_this_build()
            };
            if self.up_to_date(&sqlite, &id, &was, force)? {
                continue;
            }
            let scan = index::scan_source(&s.meta(), &self.files, Some(&sqlite))?;
            sqlite.clear_source(&id)?;
            index::load(&mut sqlite, &scan.decls)?;
            let stored = sqlite.count_source(&id)?;
            sqlite.record(&id, &Provenance { decls: stored, ..was })?;
            changed = true;
            let tag = format!(" [text]{}", anonymous_note(scan.anonymous));
            report(&s.name, scan.decls.len(), stored, &tag);
        }
        // Rebuilding the text index is minutes over 284 652 rows. Nothing
        // moved means nothing to rebuild.
        if changed {
            sqlite.finish()?;
        }
        println!("\nindex: {} ({} rows)", db.display(), sqlite.count()?);
        Ok(())
    }

    /// Read a source again and index it, which is two commands only because
    /// the reading half has two shapes: a compiled source comes from the
    /// build, a text source from its checkout.
    ///
    /// With no name this refreshes the stale sources and no others. The
    /// tempting alternative — refresh everything — is how a one-word command
    /// turns into a Mathlib dump nobody asked for.
    fn refresh(&self, source: Option<&str>) -> Result<()> {
        // Each target with what it actually needs: a source that moved has to
        // be read again, one whose rows an older `dt` wrote only has to be
        // loaded again from the dump already on disk. A source named outright
        // is read again, because that is what naming it asks for.
        let targets: Vec<(String, bool)> = match source {
            Some(n) => vec![(self.cfg.source(n)?.name.clone(), true)],
            None => {
                let repo = self.repo()?;
                let revs = OnDisk::read(&self.cfg);
                let among = self.workspace.sources.iter().map(|s| s.id.clone());
                status::stale_among(repo.as_ref(), &revs, among)?
                    .into_iter()
                    .map(|s| (s.id.as_str().to_owned(), s.why.needs_reread()))
                    .collect()
            }
        };
        if targets.is_empty() {
            println!("nothing has changed since it was indexed");
            return Ok(());
        }
        // Reported where it happens rather than in the summary: a refresh is
        // minutes long, and a reader watching one wants to know that the
        // project failed before Mathlib has finished dumping.
        let many = targets.len() > 1;
        let names: Vec<String> = targets.iter().map(|(n, _)| n.clone()).collect();
        let (read, failed) = read_each(&names, |name| {
            let reread = targets.iter().any(|(n, reread)| n == name && *reread);
            if !reread {
                // Not a dump, not a fetch: the input on disk is the right
                // input, and only the rows it turns into have changed.
                println!("{name}: indexed by an older dt, loading it again");
                return Ok(());
            }
            self.reread(name).inspect_err(|e| {
                if many {
                    eprintln!("dt: `{name}`: {e}");
                }
            })
        });
        if !read.is_empty() {
            // Forced: the source was named, or measured stale. Either way the
            // fingerprint check has already been answered, and answering it
            // again from a file this command just rewrote is how a refresh
            // does nothing.
            self.index(Some(&read), false, true)?;
        }
        outcome(targets.len(), failed)
    }

    /// Read one source again, from wherever its declarations come from: the
    /// build for a compiled source, the checkout for a fetched one. A local
    /// text source is read straight from its directory, so there is nothing
    /// to do here and the indexing that follows is the whole refresh.
    fn reread(&self, name: &str) -> Result<()> {
        let s = self.cfg.source(name)?;
        if s.elaborated() {
            self.dump(Some(name), true)
        } else if s.kind == config::Kind::Git {
            self.fetch(Some(name))
        } else {
            Ok(())
        }
    }

    /// Whether this source can be left alone. Only when its input carries a
    /// fingerprint, that fingerprint is the one already recorded, and the rows
    /// are actually there — a recorded provenance over an empty table would
    /// make `dt index` skip its way to an empty index.
    fn up_to_date(
        &self,
        db: &SqliteIndex,
        id: &SourceId,
        now: &Provenance,
        force: bool,
    ) -> Result<bool> {
        if force || now.stamp.is_none() {
            return Ok(false);
        }
        let Some(was) = db.provenance_of(id)? else { return Ok(false) };
        // The stamp answers "is the input the same input"; it cannot answer
        // "does this build read that input the way the last one did". A dump
        // that has not moved a byte still has to be loaded again when the rows
        // it turns into have changed.
        if was.stamp != now.stamp || was.outdated() || db.count_source(id)? == 0 {
            return Ok(false);
        }
        println!("{id}: unchanged, {} declarations kept", was.decls);
        Ok(true)
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

/// The source name, however it was spelled. `--source` is hidden rather than
/// removed: it is the guess a flag-shaped memory makes, and refusing it would
/// teach nothing that accepting it does not.
/// Read every target, keeping going past the ones that fail.
///
/// A toolchain bump is the moment every source in the index goes stale at
/// once, and the source refreshed first -- the project's own build, because a
/// project configures its own source first -- is the one the bump is most
/// likely to have broken. Stopping there leaves Mathlib and core on the
/// previous toolchain's declarations, which is the index the next question is
/// about to be asked of.
/// What a refresh reports once every target has been tried.
///
/// A refresh is the one command whose caller is usually not a reader: a `&&`
/// chain, a Makefile, an agent deciding whether the index it is about to
/// search can be trusted. So a source left as it was is an error and not a
/// remark, however many others were read.
///
/// One name, one failure, nothing else attempted: the reason is the whole
/// answer, and a summary over a list of one would only bury it.
fn outcome(targets: usize, mut failed: Vec<(String, Error)>) -> Result<()> {
    match failed.len() {
        0 => Ok(()),
        1 if targets == 1 => Err(failed.remove(0).1),
        n => {
            let names: Vec<&str> = failed.iter().map(|(n, _)| n.as_str()).collect();
            bail!(
                "{n} of {targets} sources could not be read and were left as they were: {}",
                names.join(", ")
            )
        }
    }
}

fn read_each(
    targets: &[String],
    mut read: impl FnMut(&str) -> Result<()>,
) -> (Vec<String>, Vec<(String, Error)>) {
    let mut ok = Vec::new();
    let mut failed = Vec::new();
    for name in targets {
        match read(name) {
            Ok(()) => ok.push(name.clone()),
            Err(e) => failed.push((name.clone(), e)),
        }
    }
    (ok, failed)
}

fn named(positional: Option<String>, flag: Option<String>) -> Option<String> {
    positional.or(flag)
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

/// The skill file, compiled in. One copy: what `dt skill` prints is the file
/// this repository ships, so the two cannot drift apart.
const SKILL: &str = include_str!("../../.claude/skills/discrtree/SKILL.md");

/// An agent that has to read `--help` for eleven commands to find out what the
/// tool does has spent more than the answer is worth. This is that, once.
fn skill(install: bool) -> Result<()> {
    if !install {
        print!("{SKILL}");
        return Ok(());
    }
    let path = PathBuf::from(".claude/skills/discrtree/SKILL.md");
    std::fs::create_dir_all(path.parent().expect("the path has a parent"))?;
    std::fs::write(&path, SKILL)?;
    println!("wrote {}", path.display());
    Ok(())
}

/// Every source a dependency listing drew on. `--depth all` keeps only the
/// tally, but the tally is by source, which is all this needs.
fn closure_sources(r: &DepsResult) -> BTreeSet<SourceId> {
    match r {
        DepsResult::Levels { root, levels, .. } => {
            std::iter::once(root).chain(levels.iter().flatten()).map(|d| d.source.clone()).collect()
        }
        DepsResult::Summary { root, stats, .. } => std::iter::once(root.source.clone())
            .chain(stats.by_source.keys().map(|s| SourceId::new(s.clone())))
            .collect(),
    }
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

/// Seconds since the Unix epoch. A clock that is before the epoch is a clock
/// problem, not an index problem; it reads as "just now" rather than failing.
fn now() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs())
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

    /// The name of the source a command was pointed at, however it was
    /// spelled.
    fn source_arg(argv: &[&str]) -> Option<String> {
        match Cli::parse_from(argv).command {
            Command::Dump { source, source_flag, .. }
            | Command::Scan { source, source_flag }
            | Command::Fetch { source, source_flag }
            | Command::Index { source, source_flag, .. }
            | Command::Refresh { source, source_flag } => named(source, source_flag),
            _ => unreachable!("not a command that takes a source"),
        }
    }

    /// `dt dump project` and `dt index` were the two halves of one action
    /// spelled two ways, and the warning that named them taught the wrong
    /// guess: `dt index --source project` used to be a usage error. Both
    /// spellings now arrive at the same source on every command that has one.
    #[test]
    fn a_source_can_be_named_positionally_or_as_a_flag() {
        for cmd in ["dump", "scan", "fetch", "index", "refresh"] {
            assert_eq!(source_arg(&["dt", cmd, "project"]).as_deref(), Some("project"), "{cmd}");
            assert_eq!(
                source_arg(&["dt", cmd, "--source", "project"]).as_deref(),
                Some("project"),
                "{cmd}"
            );
            assert_eq!(source_arg(&["dt", cmd]), None, "{cmd}");
        }
    }

    /// `--rebuild` deletes the database. Accepting a source name alongside it
    /// would read as "rebuild this one source" and do the opposite.
    #[test]
    fn rebuilding_cannot_be_narrowed_to_one_source() {
        assert!(Cli::try_parse_from(["dt", "index", "--rebuild", "project"]).is_err());
        assert!(Cli::try_parse_from(["dt", "index", "--rebuild", "--source", "project"]).is_err());
        assert!(Cli::try_parse_from(["dt", "index", "--rebuild"]).is_ok());
    }

    /// One name, two spellings, and no way to give both.
    #[test]
    fn a_source_cannot_be_named_twice() {
        assert!(Cli::try_parse_from(["dt", "index", "a", "--source", "b"]).is_err());
    }

    /// The bump that makes every source stale at once is the bump that breaks
    /// the project's own build, and the project is refreshed first. Stopping
    /// there used to leave Mathlib, Batteries and core on the previous
    /// toolchain while the command reported the one failure it hit.
    #[test]
    fn a_source_that_cannot_be_read_does_not_stop_the_others() {
        let targets: Vec<String> =
            ["project", "mathlib", "batteries", "core"].iter().map(|s| (*s).to_owned()).collect();
        let (read, failed) = read_each(&targets, |name| match name {
            "project" => Err(Error::new("incompatible header")),
            _ => Ok(()),
        });
        assert_eq!(read, ["mathlib", "batteries", "core"]);
        assert_eq!(failed.len(), 1);
        assert_eq!(failed[0].0, "project");
        assert_eq!(failed[0].1.to_string(), "incompatible header");
    }

    /// Every failure is reported, not just the first one.
    #[test]
    fn what_could_not_be_read_is_all_of_it() {
        let targets: Vec<String> = ["a", "b", "c"].iter().map(|s| (*s).to_owned()).collect();
        let (read, failed) = read_each(&targets, |name| match name {
            "b" => Ok(()),
            n => Err(Error::new(format!("no {n}"))),
        });
        assert_eq!(read, ["b"]);
        assert_eq!(failed.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(), ["a", "c"]);
    }

    /// Reported from a project whose `dt refresh` was said to exit 0 after
    /// the dump failed. Every version that has a `refresh` propagates the
    /// error, and the transcript could not be reproduced -- but nothing held
    /// the convention in place, which is what these three tests are for. A
    /// refresh is read by a `&&` chain more often than by a person.
    #[test]
    fn one_source_that_could_not_be_read_fails_with_its_own_reason() {
        let e = outcome(1, vec![("project".to_owned(), Error::new("lake env lean failed"))])
            .expect_err("a refresh that read nothing is not a success");
        assert_eq!(e.to_string(), "lake env lean failed");
    }

    /// The interesting case: Mathlib was refreshed, the project was not. The
    /// index is now half what was asked for, so the command says so.
    #[test]
    fn a_partly_refreshed_index_is_still_a_failure() {
        let e = outcome(2, vec![("project".to_owned(), Error::new("lake env lean failed"))])
            .expect_err("a source left as it was is an error");
        assert_eq!(
            e.to_string(),
            "1 of 2 sources could not be read and were left as they were: project"
        );
    }

    #[test]
    fn everything_read_is_the_only_success() {
        assert!(outcome(3, Vec::new()).is_ok());
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
