//! Phase 3. SQLite plus FTS5 over type and docstring, with plain columns for
//! the conclusion head and a side table for constants, so conditions combine
//! with `AND` and a query is milliseconds rather than a scan.

use crate::application::ports::{DeclRepo, DeclSink, Mention, Provenance};
use crate::domain::decl::{self, ArgHead, Decl, DeclKind, Shape, Span};
use crate::domain::name::{DeclName, ModuleName};
use crate::domain::query::Query;
use crate::domain::source::SourceId;
use crate::error::{Result, bail};
use rusqlite::{Connection, OptionalExtension, Row as SqlRow, params};
use std::path::Path;

const SCHEMA: &str = r#"
PRAGMA journal_mode = WAL;
PRAGMA synchronous  = NORMAL;

CREATE TABLE IF NOT EXISTS decl (
  id          INTEGER PRIMARY KEY,
  name        TEXT NOT NULL,
  source      TEXT NOT NULL,
  module      TEXT NOT NULL,
  kind        TEXT NOT NULL,
  type        TEXT NOT NULL,
  concl       TEXT,
  concl_args  TEXT NOT NULL DEFAULT '',
  doc         TEXT,
  sorry       INTEGER NOT NULL DEFAULT 0,
  line_start  INTEGER,
  line_end    INTEGER,
  elaborated  INTEGER NOT NULL DEFAULT 1
);

-- One row per (name, source, module). Two sources are two answers to the same
-- question: the same declaration can be both compiled and indexed as text. Two
-- modules within one source are two declarations, which happens in a text
-- corpus because a scanner reads `namespace` but not `variable` sections or
-- private scopes, and keying on (name, source) alone silently dropped 245 of
-- the 3401 declarations FLT contributes.
DROP INDEX IF EXISTS decl_name;
CREATE UNIQUE INDEX IF NOT EXISTS decl_ident  ON decl(name, source, module);
CREATE INDEX        IF NOT EXISTS decl_lookup ON decl(name);
CREATE INDEX        IF NOT EXISTS decl_concl  ON decl(concl);
CREATE INDEX        IF NOT EXISTS decl_module ON decl(module);
CREATE INDEX        IF NOT EXISTS decl_source ON decl(source);

-- Constants of the type. A side table rather than a string column so that
-- `--uses a,b` is two index lookups instead of two substring scans.
--
-- `WITHOUT ROWID` makes the primary key the table rather than an index beside
-- it, so both side tables are stored in `decl_id` order. Everything that reads
-- them does so by declaration, and so does the delete that replaces a source:
-- all of it is a range scan over rows that are already together, with no
-- secondary index on `decl_id` to build, maintain or store. A load writes them
-- in increasing `decl_id` too, so the rows arrive at the right edge of the
-- tree and in order.
CREATE TABLE IF NOT EXISTS uses (
  decl_id INTEGER NOT NULL REFERENCES decl(id) ON DELETE CASCADE,
  const   TEXT NOT NULL,
  PRIMARY KEY (decl_id, const)
) WITHOUT ROWID;

CREATE TABLE IF NOT EXISTS dep (
  decl_id INTEGER NOT NULL REFERENCES decl(id) ON DELETE CASCADE,
  name    TEXT NOT NULL,
  PRIMARY KEY (decl_id, name)
) WITHOUT ROWID;

-- What each source was when it was indexed. Without this the index cannot
-- answer the three questions that decide whether it can be trusted: has the
-- input changed since, is the input itself behind upstream, and did this build
-- write the rows. `writer` and `row_format` answer the third: a source can be
-- current against its upstream and still hold rows read differently from the
-- way they were written.
CREATE TABLE IF NOT EXISTS source (
  id         TEXT PRIMARY KEY,
  revision   TEXT,
  stamp      TEXT,
  indexed_at INTEGER NOT NULL,
  decls      INTEGER NOT NULL,
  writer     TEXT,
  row_format INTEGER
);
"#;

/// The shape of the database this code expects.
///
/// `CREATE TABLE IF NOT EXISTS` is not a migration: against a database written
/// by an older build it succeeds, changes nothing, and leaves every later query
/// reading columns that are not there — or worse, reading columns that are
/// there and mean something else. Refusing to open is the only honest answer,
/// and rebuilding costs minutes, which is what it would have cost to notice.
///
/// Bump this whenever `SCHEMA` changes in a way an existing file cannot satisfy.
const SCHEMA_VERSION: i64 = 3;

/// The one index the side tables have, and the one thing a load does not need.
///
/// `uses` is stored in `decl_id` order, so this is the only way to ask the
/// opposite question — which declarations mention a constant — and `--uses`
/// asks exactly that. A load drops it and [`SqliteIndex::finish`] builds it
/// again: six million rows written in `decl_id` order land in this tree at
/// positions that order says nothing about, a page fault apiece once it
/// outgrows the page cache, whereas the same index built in one pass over rows
/// already on disk is sorted work.
///
/// Dropping it must not make anything else slow. That is why both side tables
/// are clustered on `decl_id` rather than indexed on it: `clear_source` runs
/// in the middle of a load, and an index it depended on would be gone.
const SIDE_INDEXES: &str = r#"
CREATE INDEX IF NOT EXISTS uses_const ON uses(const, decl_id);
"#;

const DROP_SIDE_INDEXES: &str = r#"
DROP INDEX IF EXISTS uses_const;
"#;

/// Page cache for the duration of a bulk load, in KiB as a negative number,
/// which is how SQLite spells "bytes, not pages". The default is 2 MB, which is
/// not enough to hold the b-tree pages a batch of eight thousand rows touches.
///
/// 64 MB is where it stops mattering: 256 MB measured the same wall time and
/// three times the resident set.
const BULK_CACHE_KIB: i64 = -65_536;

/// The share of the index a load has to replace before rebuilding what it
/// invalidates costs less than maintaining it.
///
/// Both sides were measured on a 390 000-row index. Rebuilding is a fixed
/// price: `decl_fts` takes 5.9 s to rebuild and 1.0 s to optimize, `uses_const`
/// 6.6 s to drop and build again, and every one of those is paid whether the
/// load changed one row or all of them. Maintaining costs roughly the same per
/// row and nothing for the rows it does not touch — so the crossover is a
/// fraction of the index rather than a number of rows. One row in sixteen puts
/// it at twenty-four thousand there, and a project of two thousand
/// declarations an order of magnitude under it.
const REBUILD_SHARE: usize = 16;

const FTS: &str = r#"
CREATE VIRTUAL TABLE IF NOT EXISTS decl_fts
  USING fts5(name, type, doc, content='decl', content_rowid='id', tokenize='unicode61');
"#;

/// Refuse a database written by a different build rather than silently reading
/// it wrong. A file with no version and no tables is simply new.
fn check_version(conn: &Connection) -> Result<()> {
    let found: i64 =
        conn.pragma_query_value(None, "user_version", |r| r.get(0)).unwrap_or_default();
    let populated: bool = conn
        .prepare("SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = 'decl'")
        .and_then(|mut s| s.exists([]))
        .unwrap_or(false);
    if !populated || found == SCHEMA_VERSION || migrate(conn, found)? {
        return Ok(());
    }
    bail!(
        "this index was written by a different version of dt (schema {found}, this build \
         expects {SCHEMA_VERSION}); run `dt index --rebuild`"
    )
}

/// The shape changes an existing file can satisfy, applied in place.
///
/// Refusing to open is the honest answer when the rows would be read wrong, and
/// a schema bump that only adds nullable columns to `source` is the one case
/// where nothing would be: every column the old build wrote is still there and
/// still means what it did, and the two new ones read as "written by a dt that
/// did not record it" — which is exactly what that file is. Rebuilding a 1.2 GB
/// index to learn a fact the empty column already states is the cost of not
/// having this.
fn migrate(conn: &Connection, found: i64) -> Result<bool> {
    if found != 2 {
        return Ok(false);
    }
    conn.execute_batch(
        "ALTER TABLE source ADD COLUMN writer TEXT; \
         ALTER TABLE source ADD COLUMN row_format INTEGER;",
    )?;
    Ok(true)
}

pub struct SqliteIndex {
    conn: Connection,
    /// Whether the side indexes are currently dropped. See [`SIDE_INDEXES`].
    bulk: bool,
    /// Rows this load may still write before it stops maintaining the indexes
    /// and starts rebuilding them. See [`REBUILD_SHARE`].
    budget: usize,
    /// Whether `decl_fts` has been left behind by a bulk load and owes a
    /// rebuild. A maintained load never sets it, and that is what makes
    /// [`SqliteIndex::finish`] cheap after one.
    dirty: bool,
}

impl SqliteIndex {
    pub fn open(path: &Path) -> Result<SqliteIndex> {
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let conn = Connection::open(path)?;
        Self::init(conn)
    }

    /// For tests: the same schema with nothing on disk.
    pub fn in_memory() -> Result<SqliteIndex> {
        Self::init(Connection::open_in_memory()?)
    }

    fn init(conn: Connection) -> Result<SqliteIndex> {
        check_version(&conn)?;
        conn.execute_batch(SCHEMA)?;
        // FTS5 is a compile-time option. Without it everything except free-text
        // search still works, so a missing module is not fatal.
        let _ = conn.execute_batch(FTS);
        // A run that died mid-load left the side index dropped. Creating it
        // here is what makes that self-healing.
        conn.execute_batch(SIDE_INDEXES)?;
        conn.pragma_update(None, "user_version", SCHEMA_VERSION)?;
        // No budget until a load says otherwise, so a caller that writes
        // without clearing a source first — a fresh index, every test — takes
        // the bulk path it always did.
        Ok(SqliteIndex { conn, bulk: false, budget: 0, dirty: false })
    }

    /// What the source was when it was last indexed.
    pub fn provenance_of(&self, source: &SourceId) -> Result<Option<Provenance>> {
        let row = self
            .conn
            .prepare_cached(
                "SELECT revision, stamp, indexed_at, decls, writer, row_format \
                 FROM source WHERE id = ?1",
            )?
            .query_row(params![source.as_str()], |r| {
                Ok(Provenance {
                    revision: r.get(0)?,
                    stamp: r.get(1)?,
                    indexed_at: r.get::<_, i64>(2)? as u64,
                    decls: r.get::<_, i64>(3)? as usize,
                    writer: r.get(4)?,
                    row_format: r.get(5)?,
                })
            })
            .optional()?;
        Ok(row)
    }

    /// Take [`SIDE_INDEXES`] down for a load and give SQLite room to work.
    /// Idempotent: the first `put` calls it, every later one is a bool test.
    fn enter_bulk(&mut self) -> Result<()> {
        if self.bulk {
            return Ok(());
        }
        self.conn.execute_batch(DROP_SIDE_INDEXES)?;
        self.conn.pragma_update(None, "cache_size", BULK_CACHE_KIB)?;
        self.bulk = true;
        Ok(())
    }

    /// Put it back. `--uses` is a table scan until this has run.
    fn exit_bulk(&mut self) -> Result<()> {
        if !self.bulk {
            return Ok(());
        }
        self.conn.execute_batch(SIDE_INDEXES)?;
        self.bulk = false;
        Ok(())
    }

    fn has_fts(&self) -> bool {
        self.conn.prepare("SELECT 1 FROM decl_fts LIMIT 1").is_ok()
    }

    /// Drop everything from one source, so a re-index replaces rather than
    /// duplicates.
    ///
    /// Called between loads, which means the side indexes may be down — so
    /// these deletes are written to need only what a `WITHOUT ROWID` table
    /// gives them for free, which is its own `decl_id` order.
    pub fn clear_source(&mut self, source: &SourceId) -> Result<usize> {
        // The size of what is going out is the best estimate of what is coming
        // in, and it is exact for the loop this matters in: an edit re-dumps a
        // source and puts back the same declarations plus a few.
        let removing = self.count_source(source)?;
        self.budget = self.count()? / REBUILD_SHARE;
        if removing >= self.budget {
            self.enter_bulk()?;
            self.dirty = true;
        } else if self.has_fts() {
            // `decl_fts` holds no content of its own: it reads the columns out
            // of `decl`, so the rows have to leave the text index while `decl`
            // can still say what they were indexed under.
            self.conn.execute(
                "INSERT INTO decl_fts(decl_fts, rowid, name, type, doc)
                 SELECT 'delete', id, name, type, doc FROM decl WHERE source = ?1",
                params![source.as_str()],
            )?;
        }
        let tx = &self.conn;
        tx.execute(
            "DELETE FROM uses WHERE decl_id IN (SELECT id FROM decl WHERE source = ?1)",
            params![source.as_str()],
        )?;
        tx.execute(
            "DELETE FROM dep WHERE decl_id IN (SELECT id FROM decl WHERE source = ?1)",
            params![source.as_str()],
        )?;
        let n = tx.execute("DELETE FROM decl WHERE source = ?1", params![source.as_str()])?;
        Ok(n)
    }

    pub fn count(&self) -> Result<usize> {
        Ok(self.conn.query_row("SELECT count(*) FROM decl", [], |r| r.get::<_, i64>(0))? as usize)
    }

    /// Rows one source contributes. `dt index` compares this with the number it
    /// handed over: two declarations sharing an identity collapse into one row,
    /// and a corpus quietly losing a few hundred declarations is exactly the
    /// kind of thing a search tool must not hide.
    pub fn count_source(&self, source: &SourceId) -> Result<usize> {
        Ok(self.conn.query_row(
            "SELECT count(*) FROM decl WHERE source = ?1",
            params![source.as_str()],
            |r| r.get::<_, i64>(0),
        )? as usize)
    }
}

fn decl_from_row(r: &SqlRow<'_>) -> rusqlite::Result<Decl> {
    let concl: Option<String> = r.get("concl")?;
    let args: String = r.get("concl_args")?;
    let start: Option<u32> = r.get("line_start")?;
    let end: Option<u32> = r.get("line_end")?;
    Ok(Decl {
        name: DeclName::new(r.get::<_, String>("name")?),
        source: SourceId::new(r.get::<_, String>("source")?),
        module: ModuleName::new(r.get::<_, String>("module")?),
        kind: DeclKind::parse(&r.get::<_, String>("kind")?),
        ty: r.get("type")?,
        shape: Shape::new(
            concl.map(DeclName::new),
            args.split_whitespace().map(ArgHead::parse).collect(),
        ),
        consts: Vec::new(),
        deps: Vec::new(),
        doc: r.get("doc")?,
        has_sorry: r.get::<_, i64>("sorry")? != 0,
        span: match (start, end) {
            (Some(a), Some(b)) => Some(Span::new(a, b)),
            _ => None,
        },
        elaborated: r.get::<_, i64>("elaborated")? != 0,
    })
}

impl SqliteIndex {
    /// Fill in the two side tables for rows already read. Done in one statement
    /// per batch: `dt deps` on a 5154-node closure would otherwise be 5154
    /// round trips.
    fn attach_lists(&self, decls: &mut [Decl]) -> Result<()> {
        if decls.is_empty() {
            return Ok(());
        }
        let mut by_name: std::collections::HashMap<String, Vec<usize>> = Default::default();
        for (i, d) in decls.iter().enumerate() {
            by_name.entry(d.name.to_string()).or_default().push(i);
        }
        let placeholders = vec!["?"; decls.len()].join(",");
        let names: Vec<String> = decls.iter().map(|d| d.name.to_string()).collect();
        let bind: Vec<&dyn rusqlite::ToSql> =
            names.iter().map(|n| n as &dyn rusqlite::ToSql).collect();

        for (table, column) in [("uses", "const"), ("dep", "name")] {
            let sql = format!(
                "SELECT d.name, t.{column} FROM decl d JOIN {table} t ON t.decl_id = d.id \
                 WHERE d.name IN ({placeholders})"
            );
            let mut stmt = self.conn.prepare(&sql)?;
            let mut rows = stmt.query(bind.as_slice())?;
            while let Some(row) = rows.next()? {
                let owner: String = row.get(0)?;
                let value: String = row.get(1)?;
                if let Some(idx) = by_name.get(&owner) {
                    for i in idx {
                        let list = if table == "uses" {
                            &mut decls[*i].consts
                        } else {
                            &mut decls[*i].deps
                        };
                        list.push(DeclName::new(value.clone()));
                    }
                }
            }
        }
        Ok(())
    }
}

impl DeclRepo for SqliteIndex {
    fn get(&self, name: &DeclName) -> Result<Option<Decl>> {
        // Compiled rows win over text rows for the same name: an elaborated
        // answer is strictly better than a guessed one.
        let mut decl = self
            .conn
            .prepare_cached("SELECT * FROM decl WHERE name = ?1 ORDER BY elaborated DESC LIMIT 1")?
            .query_row(params![name.as_str()], decl_from_row)
            .optional()?;
        if let Some(d) = decl.as_mut() {
            self.attach_lists(std::slice::from_mut(d))?;
        }
        Ok(decl)
    }

    /// One scan of `decl`, counted in Rust.
    ///
    /// `concl` is indexed and `concl_args` is a space-joined list, so neither
    /// a suffix nor a member test can use an index; both `LIKE`s are there to
    /// cut the rows that reach the counting, not to decide anything. They also
    /// over-match -- `_` is a wildcard to `LIKE` and a letter in half the
    /// names in Mathlib -- which costs a few rows and changes no answer,
    /// because what a head is called is decided again in `commonest_called`.
    fn heads_called(&self, word: &str) -> Result<Vec<DeclName>> {
        let ends = format!("%.{word}");
        let mentions = format!("%.{word}%");
        let mut stmt = self.conn.prepare_cached(
            "SELECT concl, concl_args FROM decl WHERE concl LIKE ?1 OR concl_args LIKE ?2",
        )?;
        let mut heads: Vec<DeclName> = Vec::new();
        let mut rows = stmt.query(params![ends, mentions])?;
        while let Some(row) = rows.next()? {
            let concl: Option<String> = row.get(0)?;
            let args: String = row.get(1)?;
            heads.extend(concl.into_iter().map(DeclName::new));
            heads.extend(args.split_whitespace().map(DeclName::new));
        }
        Ok(decl::commonest_called(heads.iter(), word))
    }

    fn enclosing(&self, of: &Decl) -> Result<Option<Decl>> {
        let Some(span) = of.span else { return Ok(None) };
        // Smallest container, so a lemma generated inside a theorem that is
        // itself inside a section reports the theorem. `decl_module` narrows
        // this to one file's worth of rows before the range test runs.
        self.conn
            .prepare_cached(
                "SELECT * FROM decl
                 WHERE module = ?1 AND source = ?2 AND name <> ?3
                   AND line_start <= ?4 AND line_end >= ?5
                   AND (line_start < ?4 OR line_end > ?5)
                 ORDER BY line_end - line_start LIMIT 1",
            )?
            .query_row(
                params![
                    of.module.as_str(),
                    of.source.as_str(),
                    of.name.as_str(),
                    span.start,
                    span.end
                ],
                decl_from_row,
            )
            .optional()
            .map_err(Into::into)
    }

    fn contains(&self, name: &DeclName) -> Result<bool> {
        Ok(self
            .conn
            .prepare_cached("SELECT 1 FROM decl WHERE name = ?1 LIMIT 1")?
            .query_row(params![name.as_str()], |_| Ok(()))
            .optional()?
            .is_some())
    }

    fn get_many(&self, names: &[DeclName]) -> Result<Vec<Decl>> {
        if names.is_empty() {
            return Ok(Vec::new());
        }
        let mut out = Vec::with_capacity(names.len());
        // Chunked to stay under SQLITE_MAX_VARIABLE_NUMBER on a closure of
        // thousands of names.
        for chunk in names.chunks(500) {
            let placeholders = vec!["?"; chunk.len()].join(",");
            let sql = format!(
                "SELECT * FROM decl WHERE name IN ({placeholders}) ORDER BY elaborated DESC"
            );
            let strings: Vec<String> = chunk.iter().map(DeclName::to_string).collect();
            let bind: Vec<&dyn rusqlite::ToSql> =
                strings.iter().map(|s| s as &dyn rusqlite::ToSql).collect();
            let mut stmt = self.conn.prepare(&sql)?;
            let rows = stmt.query_map(bind.as_slice(), decl_from_row)?;
            for r in rows {
                out.push(r?);
            }
        }
        self.attach_lists(&mut out)?;
        // Keep the order asked for: `dt add` depends on it being topological.
        let position: std::collections::HashMap<&DeclName, usize> =
            names.iter().enumerate().map(|(i, n)| (n, i)).collect();
        out.sort_by_key(|d| position.get(&d.name).copied().unwrap_or(usize::MAX));
        out.dedup_by(|a, b| a.name == b.name);
        Ok(out)
    }

    fn find(&self, query: &Query) -> Result<Vec<Decl>> {
        let (sql, binds) = build_sql(query, self.has_fts());
        let mut stmt = self.conn.prepare(&sql)?;
        let bind: Vec<&dyn rusqlite::ToSql> =
            binds.iter().map(|s| s as &dyn rusqlite::ToSql).collect();
        let rows = stmt.query_map(bind.as_slice(), decl_from_row)?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        self.attach_lists(&mut out)?;
        // Argument shape is checked in the domain: it is positional matching
        // with an alignment search, which SQL would express badly and slowly.
        out.retain(|d| query.shape.matches(&d.shape));
        Ok(out)
    }

    fn provenance(&self, source: &SourceId) -> Result<Option<Provenance>> {
        self.provenance_of(source)
    }

    /// `dep` has no index on `name`: it would be the size of the table again,
    /// twelve million rows in a Mathlib index, for a question asked before a
    /// refactor rather than on every search. The scan is a second warm.
    fn used_by(&self, name: &DeclName, within: &Query) -> Result<Vec<Mention>> {
        let mut filter = String::new();
        let mut binds: Vec<String> = vec![name.to_string()];
        if let Some(s) = &within.source {
            filter.push_str(" AND d.source = ?");
            binds.push(s.to_string());
        }
        if let Some(m) = &within.module {
            filter.push_str(" AND (d.module = ? OR d.module LIKE ?)");
            binds.push(m.clone());
            binds.push(format!("{m}.%"));
        }
        if !within.generated {
            filter.push_str(&format!(" AND {NOT_GENERATED}"));
            binds.push(decl::GENERATED_ELIM.into());
        }
        let sql = format!(
            "SELECT d.name, d.source, d.module, d.kind, d.elaborated, \
             EXISTS (SELECT 1 FROM uses u WHERE u.decl_id = d.id AND u.const = ?1) \
             FROM decl d WHERE d.id IN (SELECT decl_id FROM dep WHERE name = ?1 \
             UNION SELECT decl_id FROM uses WHERE const = ?1){filter}"
        );
        let mut stmt = self.conn.prepare(&sql)?;
        let bind: Vec<&dyn rusqlite::ToSql> =
            binds.iter().map(|s| s as &dyn rusqlite::ToSql).collect();
        let rows = stmt.query_map(bind.as_slice(), |r| {
            let mut d = Decl::stub(
                &r.get::<_, String>(0)?,
                &r.get::<_, String>(1)?,
                &r.get::<_, String>(2)?,
            );
            d.kind = DeclKind::parse(&r.get::<_, String>(3)?);
            d.elaborated = r.get(4)?;
            Ok(Mention { decl: d, in_statement: r.get(5)? })
        })?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        Ok(out)
    }

    fn counts(&self) -> Result<Vec<(SourceId, usize)>> {
        let mut stmt = self
            .conn
            .prepare("SELECT source, count(*) FROM decl GROUP BY source ORDER BY source")?;
        let rows = stmt.query_map([], |r| {
            Ok((SourceId::new(r.get::<_, String>(0)?), r.get::<_, i64>(1)? as usize))
        })?;
        let mut out = Vec::new();
        for r in rows {
            out.push(r?);
        }
        Ok(out)
    }
}

/// Translate a [`Query`] into SQL. Separate from the connection so it can be
/// tested without one.
/// `Decl::is_generated`, spelled for SQL, with one bind: `GENERATED_ELIM`.
/// `_` is a LIKE wildcard, so the names with an underscore in them escape it.
const NOT_GENERATED: &str = "NOT (d.name LIKE '%.ctorIdx' OR d.name LIKE '%.ctorElim' \
     OR d.name LIKE '%.ctorElimType' OR d.name LIKE '%.congr!_simp' ESCAPE '!' \
     OR d.name LIKE '%.ofNat!_ctorIdx' ESCAPE '!' OR d.name LIKE '%.brecOn.%' \
     OR (d.name LIKE '%.elim' AND instr(d.type, ?) > 0))";

fn build_sql(q: &Query, has_fts: bool) -> (String, Vec<String>) {
    let mut where_clauses: Vec<String> = Vec::new();
    let mut binds: Vec<String> = Vec::new();

    if let Some(n) = &q.name {
        where_clauses.push("lower(d.name) LIKE ?".into());
        binds.push(format!("%{}%", n.to_lowercase()));
    }
    if let Some(c) = &q.shape.concl {
        where_clauses.push("d.concl = ?".into());
        binds.push(c.to_string());
    }
    // Every named argument head has to appear among the conclusion's argument
    // heads. This is a necessary condition, not the positional match itself —
    // the alignment search in the domain still decides — but pushing it down is
    // what lets a shape query see the whole corpus instead of the first `cap`
    // rows that happen to share a conclusion. `LE.le` alone matches tens of
    // thousands of declarations.
    for a in &q.shape.args {
        if let ArgHead::Named(n) = a {
            where_clauses.push("(' ' || d.concl_args || ' ') LIKE ?".into());
            binds.push(format!("% {} %", n.as_str()));
        }
    }
    for c in &q.uses {
        where_clauses
            .push("EXISTS (SELECT 1 FROM uses u WHERE u.decl_id = d.id AND u.const = ?)".into());
        binds.push(c.to_string());
    }
    if let Some(m) = &q.module {
        where_clauses.push("(d.module = ? OR d.module LIKE ?)".into());
        binds.push(m.clone());
        binds.push(format!("{m}.%"));
    }
    if let Some(s) = &q.source {
        where_clauses.push("d.source = ?".into());
        binds.push(s.to_string());
    }
    if !q.kind.is_empty() {
        let marks = vec!["?"; q.kind.len()].join(", ");
        where_clauses.push(format!("d.kind IN ({marks})"));
        binds.extend(q.kind.iter().map(|k| k.to_string()));
    }
    if q.elaborated_only || q.needs_shape() {
        where_clauses.push("d.elaborated = 1".into());
    }
    if q.needs_shape() {
        where_clauses.push("d.concl IS NOT NULL".into());
    }
    if q.no_sorry {
        where_clauses.push("d.sorry = 0".into());
    }
    if !q.generated {
        where_clauses.push(NOT_GENERATED.into());
        binds.push(decl::GENERATED_ELIM.into());
    }
    if !q.text.is_empty() {
        if has_fts {
            // One MATCH for every word: FTS5 already ANDs the terms of a query,
            // so the words go into one expression rather than one subquery each.
            where_clauses
                .push("d.id IN (SELECT rowid FROM decl_fts WHERE decl_fts MATCH ?)".into());
            binds.push(fts_query(&q.text));
        } else {
            for t in &q.text {
                where_clauses
                    .push("(lower(d.type) LIKE ? OR lower(coalesce(d.doc,'')) LIKE ?)".into());
                binds.push(format!("%{}%", t.to_lowercase()));
                binds.push(format!("%{}%", t.to_lowercase()));
            }
        }
    }

    let filter = if where_clauses.is_empty() {
        String::new()
    } else {
        format!(" WHERE {}", where_clauses.join(" AND "))
    };
    // Over-fetch, because the ranking and the positional argument match happen
    // in the domain: cutting to `limit` here would drop better answers. The cap
    // is wider when the domain still has a shape to check, since an unknown
    // fraction of what comes back will fail it.
    let cap =
        if q.shape.args.is_empty() { (q.limit * 20).max(200) } else { (q.limit * 20).max(20_000) };
    // Which rows the domain gets to rank, not what it ranks them as. `--name`
    // is a substring filter, and the row called exactly what was asked for can
    // sit anywhere among tens of thousands that merely contain it -- outside
    // the window, it is not ranked first, it is absent. The three terms mirror
    // `query::rank`, so the window is filled with the rows it would choose.
    // The `_` in a name is a LIKE wildcard and over-matches here; that changes
    // which rows are offered, never which one wins.
    let order = match &q.name {
        Some(n) => {
            let n = n.to_lowercase();
            binds.push(n.clone());
            binds.push(format!("%.{n}"));
            binds.push(format!("{n}%"));
            " ORDER BY (lower(d.name) = ?) DESC, (lower(d.name) LIKE ?) DESC, \
             (lower(d.name) LIKE ?) DESC, length(d.name)"
        }
        None => "",
    };
    (format!("SELECT d.* FROM decl d{filter}{order} LIMIT {cap}"), binds)
}

/// FTS5 treats bare punctuation as syntax. Quoting every term makes a search
/// for `↔` or `Real.exp` do what the user meant instead of failing. Terms
/// separated by a space are ANDed, which is what several `--text` mean.
fn fts_query(words: &[String]) -> String {
    words.iter().map(|t| format!("\"{}\"", t.replace('"', "\"\""))).collect::<Vec<_>>().join(" ")
}

impl DeclSink for SqliteIndex {
    fn record(&mut self, source: &SourceId, was: &Provenance) -> Result<()> {
        self.conn
            .prepare_cached(
                "INSERT OR REPLACE INTO source \
             (id, revision, stamp, indexed_at, decls, writer, row_format) \
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7)",
            )?
            .execute(params![
                source.as_str(),
                was.revision.as_deref(),
                was.stamp.as_deref(),
                was.indexed_at as i64,
                was.decls as i64,
                was.writer.as_deref(),
                was.row_format
            ])?;
        Ok(())
    }

    fn put(&mut self, decls: &[Decl]) -> Result<()> {
        // A load that turns out bigger than the source it replaced gives up
        // maintaining partway through: what it has maintained so far the
        // rebuild simply does again.
        if decls.len() > self.budget {
            self.enter_bulk()?;
            self.dirty = true;
        }
        self.budget = self.budget.saturating_sub(decls.len());
        let maintain = !self.bulk && self.has_fts();
        let tx = self.conn.transaction()?;
        {
            let mut insert = tx.prepare_cached(
                "INSERT OR REPLACE INTO decl
                 (name, source, module, kind, type, concl, concl_args, doc, sorry,
                  line_start, line_end, elaborated)
                 VALUES (?1,?2,?3,?4,?5,?6,?7,?8,?9,?10,?11,?12)",
            )?;
            // `OR IGNORE` because the side tables are keyed on (decl_id, value)
            // now. Both producers already deduplicate — the dumper because
            // `getUsedConstants` visits a constant once, the scanner because it
            // checks before it pushes — so this discards nothing. It is here so
            // that a producer which stops deduplicating loses a duplicate row
            // rather than the whole load.
            let mut insert_use =
                tx.prepare_cached("INSERT OR IGNORE INTO uses (decl_id, const) VALUES (?1, ?2)")?;
            let mut insert_dep =
                tx.prepare_cached("INSERT OR IGNORE INTO dep (decl_id, name) VALUES (?1, ?2)")?;
            // Prepared only on the maintained path: without the FTS5 module
            // these do not compile, and that is a database `dt` still works on.
            let mut replaced = maintain
                .then(|| {
                    tx.prepare_cached(
                        "SELECT id, name, type, doc FROM decl
                         WHERE name = ?1 AND source = ?2 AND module = ?3",
                    )
                })
                .transpose()?;
            let mut fts_delete = maintain
                .then(|| {
                    tx.prepare_cached(
                        "INSERT INTO decl_fts(decl_fts, rowid, name, type, doc)
                         VALUES ('delete', ?1, ?2, ?3, ?4)",
                    )
                })
                .transpose()?;
            let mut fts_insert = maintain
                .then(|| {
                    tx.prepare_cached(
                        "INSERT INTO decl_fts(rowid, name, type, doc) VALUES (?1, ?2, ?3, ?4)",
                    )
                })
                .transpose()?;
            for d in decls {
                // `INSERT OR REPLACE` frees the row it replaces and the text
                // index does not hear about it, so a row that survives a load
                // under the same key has to leave the index before it is
                // rewritten — and it can only leave it by the values it went in
                // under, which nothing but `decl` still holds.
                if let (Some(find), Some(del)) = (&mut replaced, &mut fts_delete) {
                    let was = find
                        .query_row(
                            params![d.name.as_str(), d.source.as_str(), d.module.as_str()],
                            |r| {
                                Ok((
                                    r.get::<_, i64>(0)?,
                                    r.get::<_, String>(1)?,
                                    r.get::<_, String>(2)?,
                                    r.get::<_, Option<String>>(3)?,
                                ))
                            },
                        )
                        .optional()?;
                    if let Some((id, name, ty, doc)) = was {
                        del.execute(params![id, name, ty, doc])?;
                    }
                }
                let args: Vec<&str> = d.shape.args.iter().map(ArgHead::as_str).collect();
                insert.execute(params![
                    d.name.as_str(),
                    d.source.as_str(),
                    d.module.as_str(),
                    d.kind.as_str(),
                    d.ty,
                    d.shape.concl.as_ref().map(DeclName::as_str),
                    args.join(" "),
                    d.doc,
                    d.has_sorry as i64,
                    d.span.map(|s| s.start),
                    d.span.map(|s| s.end),
                    d.elaborated as i64,
                ])?;
                // A replaced row is deleted and re-inserted, so this id is
                // always fresh and its side rows are always new. Clearing them
                // per row deleted nothing. Replacing a source is
                // `clear_source`'s job.
                let id = tx.last_insert_rowid();
                for c in &d.consts {
                    insert_use.execute(params![id, c.as_str()])?;
                }
                for c in &d.deps {
                    insert_dep.execute(params![id, c.as_str()])?;
                }
                if let Some(ins) = &mut fts_insert {
                    ins.execute(params![id, d.name.as_str(), d.ty, d.doc])?;
                }
            }
        }
        tx.commit()?;
        Ok(())
    }

    fn finish(&mut self) -> Result<()> {
        self.exit_bulk()?;
        if !self.dirty {
            // Nothing here has anything to do after a maintained load: the
            // text index is already current, and the planner has nothing to
            // learn from a change of half a percent. Doing it anyway is the
            // fourteen seconds this branch exists to not spend.
            return Ok(());
        }
        // A bulk load leaves the text index empty and stale by turns, so it is
        // built once at the end: maintaining it row by row roughly doubles the
        // load time for half a million rows.
        if self.has_fts() {
            self.conn.execute_batch(
                "INSERT INTO decl_fts(decl_fts) VALUES('rebuild');
                 INSERT INTO decl_fts(decl_fts) VALUES('optimize');",
            )?;
        }
        self.conn.execute_batch("ANALYZE;")?;
        self.dirty = false;
        Ok(())
    }
}
