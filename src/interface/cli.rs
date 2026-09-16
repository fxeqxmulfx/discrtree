//! Argument parsing only.

use clap::{Args, Parser, Subcommand};
use std::ffi::OsString;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    name = "dt",
    version,
    about = "Find a Lean declaration by shape, and lift it into a proof",
    long_about = "discrtree indexes Lean corpora and answers two questions \
                  without loading the Lean environment: where is the declaration \
                  with this shape, and what does it take to use it here. \
                  Mathlib's `#find` answers the first only over what the file \
                  has already imported, which is the wrong set when the point \
                  of the search is to find out what to import.\n\n\
                  Compiled sources are elaborated: shape search and exact \
                  dependencies work. Text sources are not, and every row from \
                  one is marked [text]. Asking for a shape implies \
                  --elaborated, because a text row cannot answer that \
                  question.\n\n\
                  Set up once, in this order:\n\
                  \x20 dt init      write discrtree.toml, then edit it\n\
                  \x20 dt fetch     clone the text corpora\n\
                  \x20 dt dump      run Lean over the compiled ones (minutes)\n\
                  \x20 dt index     build the index\n\n\
                  After that `dt index` is free unless something moved, and \
                  `dt status` says what has."
)]
pub struct Cli {
    /// Path to discrtree.toml. Found by searching upwards when omitted.
    #[arg(long, global = true, value_name = "FILE", display_order = 900)]
    pub config: Option<PathBuf>,

    /// Report what is being done, on stderr.
    #[arg(short, long, global = true, display_order = 901)]
    pub verbose: bool,

    #[command(subcommand)]
    pub command: Command,
}

impl Cli {
    /// The command line, with a pattern that starts with a negation read as the
    /// pattern it is.
    ///
    /// `dt find '-_ * _ = _'` was refused: to the parser an argument that
    /// starts with `-` is a flag, and no flag is spelled `-_`. Taking hyphens
    /// as the start of a pattern outright takes every misspelt flag for one
    /// too, and `--elaborted` searched for itself. So the command line is read
    /// as written first, and only when that fails is an argument of `find` no
    /// flag is spelled like -- a `-` and anything but letters after it -- read
    /// again from behind a `--`. The error is the one the line as written got.
    pub fn read(argv: Vec<OsString>) -> Result<Cli, clap::Error> {
        let err = match Cli::try_parse_from(&argv) {
            Ok(cli) => return Ok(cli),
            Err(e) => e,
        };
        let Some(i) = negation(&argv) else { return Err(err) };
        let mut moved = argv;
        let pattern = moved.remove(i);
        moved.extend([OsString::from("--"), pattern]);
        Cli::try_parse_from(moved).map_err(|_| err)
    }
}

/// Where the argument of `dt find` is that starts with a `-` no flag can,
/// unless a `--` is already there to say what is a flag.
fn negation(argv: &[OsString]) -> Option<usize> {
    let find = argv.iter().position(|a| a == "find")?;
    if argv.iter().any(|a| a == "--") {
        return None;
    }
    (find + 1..argv.len()).find(|i| {
        argv[*i].to_str().and_then(|a| a.strip_prefix('-')).is_some_and(|rest| {
            !rest.starts_with('-') && rest.chars().any(|c| !c.is_ascii_alphabetic())
        })
    })
}

#[derive(Subcommand, Debug)]
pub enum Command {
    /// Write a starter discrtree.toml.
    Init {
        /// Overwrite an existing file.
        #[arg(long)]
        force: bool,
    },

    /// Print the agent skill for this tool: the whole interface, in 30 lines.
    ///
    /// Written for a program rather than a person. `--install` writes it to
    /// .claude/skills/discrtree/SKILL.md, where an agent loads it when it is
    /// needed instead of carrying it in every prompt.
    Skill {
        /// Write it to .claude/skills/discrtree/SKILL.md instead of printing.
        #[arg(long)]
        install: bool,
    },

    /// Dump a compiled source from the Lean environment into JSONL.
    Dump {
        /// Source name. All compiled sources when omitted.
        source: Option<String>,
        /// Spelling the positional name as a flag, for the hands that reach
        /// for `--source` first. Hidden: `--help` should teach one spelling.
        #[arg(long = "source", value_name = "SOURCE", conflicts_with = "source", hide = true)]
        source_flag: Option<String>,
        /// Skip proof terms: a much faster dump, with no dependency lists.
        #[arg(long)]
        no_deps: bool,
    },

    /// Read a text source with the scanner. Nothing here runs Lean.
    Scan {
        /// Source name. All text sources when omitted.
        source: Option<String>,
        /// Spelling the positional name as a flag, for the hands that reach
        /// for `--source` first. Hidden: `--help` should teach one spelling.
        #[arg(long = "source", value_name = "SOURCE", conflicts_with = "source", hide = true)]
        source_flag: Option<String>,
    },

    /// Clone or update a text source.
    Fetch {
        /// Source name. All git sources when omitted.
        source: Option<String>,
        /// Spelling the positional name as a flag, for the hands that reach
        /// for `--source` first. Hidden: `--help` should teach one spelling.
        #[arg(long = "source", value_name = "SOURCE", conflicts_with = "source", hide = true)]
        source_flag: Option<String>,
    },

    /// Build the search index from whatever has been dumped and scanned.
    ///
    /// A source whose input has not changed since it was indexed is left
    /// alone. Re-reading a 700 MB dump to discover that it is the same dump is
    /// the slowest way to do nothing.
    Index {
        /// Source name. Every source with anything new when omitted.
        source: Option<String>,
        /// Spelling the positional name as a flag, for the hands that reach
        /// for `--source` first. Hidden: `--help` should teach one spelling.
        #[arg(long = "source", value_name = "SOURCE", conflicts_with = "source", hide = true)]
        source_flag: Option<String>,
        /// Delete the index and start over. Needed when the schema changes.
        ///
        /// Not compatible with a source name: this deletes the whole database,
        /// which is the opposite of what naming one source asks for.
        #[arg(long, conflicts_with_all = ["source", "source_flag"])]
        rebuild: bool,
        /// Re-index every source, including the ones that have not changed.
        #[arg(long)]
        force: bool,
    },

    /// Read a source again and index it: the two commands the staleness
    /// warning used to name, as the one action they always were.
    ///
    /// Which two depends on the source and is the reason this exists: a
    /// compiled source is read from the build by `dt dump`, a text source from
    /// its checkout by `dt fetch`, and only `dt index` is common to both.
    ///
    /// A named source is refreshed whether or not it looks stale, because the
    /// reason to name one is that you know something the timestamps do not.
    /// With no name, exactly the sources that have fallen behind — never all
    /// of them, which would mean dumping Mathlib again for nothing.
    ///
    /// Exit status is what a `&&` chain reads: 0 only when every source it
    /// tried was read and indexed, and 0 as well when none had fallen behind.
    /// A source that could not be read exits non-zero with the reason on
    /// stderr; over several targets each failure is named as it happens, the
    /// last line says how many of how many were left as they were, and the
    /// sources that did refresh stay refreshed.
    Refresh {
        /// Source name. Every stale source when omitted.
        source: Option<String>,
        /// Spelling the positional name as a flag, for the hands that reach
        /// for `--source` first. Hidden: `--help` should teach one spelling.
        #[arg(long = "source", value_name = "SOURCE", conflicts_with = "source", hide = true)]
        source_flag: Option<String>,
    },

    /// What is indexed, whether it is elaborated, and whether it is current.
    ///
    /// Each source reports the revision it was indexed from next to the one it
    /// is at now. A source that has moved since is named, because a stale index
    /// answers confidently and wrongly. The project's own revision fingerprints
    /// its build, so a module compiled since the last dump shows up here too.
    ///
    /// The lake packages the build resolved that no source covers are listed
    /// last, and under them the toolchain, whose `Init` and `Std` are a corpus
    /// with no directory to be listed from at all. Every declaration in either
    /// is importable from the project and in no search, which is the one gap
    /// the index cannot report on its own.
    Status,

    /// Print a declaration and the import line that provides it.
    ///
    /// Several names at once cost one invocation instead of one each, which is
    /// the expensive part when this is driven by a program.
    Show {
        /// Fully qualified declaration names, e.g. Real.exp_le_exp.
        #[arg(required = true, value_name = "NAME")]
        names: Vec<String>,
        /// Print only the import lines, deduplicated.
        #[arg(long)]
        import_only: bool,
        /// Accepted and ignored. `--long` is a `find` flag, and `show` is
        /// already long: it prints the declaration's own source, docstring and
        /// proof included. Taken rather than refused because refusing it costs
        /// the caller a round trip to learn that it had the answer already.
        #[arg(long, hide = true)]
        long: bool,
    },

    /// What a proof rests on, level by level.
    ///
    /// Exact for an elaborated source — these are the constants the proof term
    /// actually uses. For a text source they are guessed from the file's
    /// imports and marked as guessed.
    Deps {
        /// Fully qualified declaration name.
        name: String,
        /// Levels to print. `all` gives the size of the closure instead of
        /// printing it.
        #[arg(long, value_name = "N|all", default_value = "1")]
        depth: String,
    },

    /// What rests on a declaration: everything whose statement or proof
    /// mentions it.
    ///
    /// The reverse of `deps`, one level deep, grouped by module. A name marked
    /// `*` mentions it in its statement, which is all `find --uses` can see.
    Rdeps {
        /// Fully qualified declaration name.
        name: String,
        /// Module prefix, e.g. Transformer.CRASP.
        #[arg(long = "in", value_name = "MODULE")]
        module: Option<String>,
        /// Restrict to one source, as named in discrtree.toml.
        #[arg(long, value_name = "NAME")]
        source: Option<String>,
        /// Include names the compiler generated.
        #[arg(long)]
        generated: bool,
        /// Maximum names listed. The first line says how many there are in all.
        #[arg(long, value_name = "N", default_value_t = 100)]
        limit: usize,
    },

    /// Materialize a declaration and its tree into the project.
    ///
    /// The tree stops at the importable frontier: a dependency that can be
    /// imported becomes one import line and its whole subtree disappears. That
    /// is why the answer for a Mathlib lemma is a single line rather than 5000
    /// declarations.
    Add {
        /// Fully qualified declaration name.
        name: String,
        /// Actually write. Without it this is a dry run, which is the default
        /// because the depth of the tree cannot be predicted from the name.
        #[arg(long)]
        write: bool,
        /// Replace files that already exist.
        #[arg(long)]
        force: bool,
    },

    /// Search: by shape, name, constants, module or text
    ///
    /// A pattern is the shape of a statement, written the way it reads:
    ///
    ///   dt find 'Real.exp _ ≤ _'        conclusion ≤, left side headed by Real.exp
    ///   dt find 'Finset.sum _ _ = _'    conclusion =, left side headed by Finset.sum
    ///   dt find 'Nat.Prime _'           no notation: Nat.Prime is the conclusion
    ///
    /// `_` is anything. The top-level notation symbol becomes the conclusion
    /// head — ≤ < ≥ > = ≠ ↔ ∈ ⊆ ∣ + - * / ^ % ∧ ∨ → ∑ ∏ ⊓ ⊔ ‖ — and the head
    /// identifier of each side becomes an argument. Identifiers anywhere else
    /// become --uses conditions rather than being dropped. A field is its name
    /// in any namespace: `l.length` is `.length` applied to `_`. `-v` prints
    /// what the pattern was read as.
    ///
    /// Conditions combine with AND, and a pattern may be mixed with any flag.
    /// Asking for a shape implies --elaborated: a text row has no conclusion
    /// head symbol, so including it would silently drop the condition.
    ///
    /// An empty result says which condition to blame — the one that matches
    /// nothing on its own, or none of them when it is the combination that is
    /// empty.
    #[command(verbatim_doc_comment)]
    Find(FindArgs),

    /// Look for declarations in a file that upstream already has.
    Dup {
        /// A .lean file in the project.
        file: PathBuf,
        /// Minimum overlap of constants to report, in 0.0..=1.0.
        #[arg(long, default_value_t = 0.5)]
        threshold: f32,
    },
}

#[derive(Args, Debug)]
pub struct FindArgs {
    /// A pattern, e.g. 'Real.exp _ ≤ _'.
    pub pattern: Option<String>,

    /// Substring of the declaration name, case-insensitive.
    #[arg(long, value_name = "SUBSTRING")]
    pub name: Option<String>,

    /// Head symbol of the conclusion, e.g. LE.le, or .Nodup in any namespace.
    /// Implies --elaborated.
    #[arg(long, value_name = "HEAD")]
    pub concl: Option<String>,

    /// Constants the type must mention, e.g. Real.exp,Finset.sum, or .length in
    /// any namespace. All of them.
    /// The statement only: `dt rdeps` finds what mentions a constant in a proof.
    #[arg(long, value_delimiter = ',', value_name = "CONST,...")]
    pub uses: Vec<String>,

    /// Module prefix, e.g. Mathlib.Analysis. A whole prefix from the root, not
    /// a fragment: `Analysis` matches nothing.
    #[arg(long = "in", value_name = "MODULE")]
    pub module: Option<String>,

    /// Restrict to one source, as named in discrtree.toml. `dt status` lists them.
    #[arg(long, value_name = "NAME")]
    pub source: Option<String>,

    /// Any of: theorem, def, structure, inductive, axiom, instance, ctor,
    /// opaque, rec, quot. A comma list or repeated means any of them. `lemma`
    /// is indexed as theorem, `abbrev` as def, `class` as structure.
    #[arg(long, value_delimiter = ',', value_name = "KIND,...")]
    pub kind: Vec<String>,

    /// Free text over the name, type and docstring of each declaration; module
    /// docstrings are not read. Whole words, not substrings.
    /// Repeatable, and several words in one --text mean the same thing: all of
    /// them must appear.
    #[arg(long, value_name = "WORDS")]
    pub text: Vec<String>,

    /// Only rows that came out of the elaborator.
    #[arg(long)]
    pub elaborated: bool,

    /// Drop declarations proved by sorry.
    #[arg(long)]
    pub no_sorry: bool,

    /// Include names the compiler generated (ctorIdx, congr_simp, T.ctor.elim, ...),
    /// which are hidden otherwise.
    #[arg(long)]
    pub generated: bool,

    /// Maximum results. The footer says when more matched than were shown.
    #[arg(long, value_name = "N", default_value_t = crate::domain::query::DEFAULT_LIMIT)]
    pub limit: usize,

    /// The untruncated type of every hit, and its docstring. Measured at
    /// about a third more output.
    #[arg(long)]
    pub long: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(argv: &[&str]) -> Result<Cli, clap::Error> {
        Cli::read(argv.iter().map(OsString::from).collect())
    }

    /// `-_ * _ = _` could not be typed: it was an unknown flag `-_`. It reads
    /// as a pattern wherever it is written, and a misspelt flag still reads as
    /// the mistake it is.
    #[test]
    fn a_pattern_may_start_with_a_negation() {
        for argv in [
            &["dt", "find", "-_ * _ = _", "--limit", "3"][..],
            &["dt", "-v", "find", "--limit", "3", "-_ * _ = _"],
        ] {
            let Command::Find(a) = read(argv).unwrap().command else { panic!("{argv:?}") };
            assert_eq!(a.pattern.as_deref(), Some("-_ * _ = _"), "{argv:?}");
            assert_eq!(a.limit, 3, "{argv:?}");
        }
        let err = read(&["dt", "find", "--elaborted"]).unwrap_err().to_string();
        assert!(err.contains("'--elaborted'"), "{err}");
        assert!(read(&["dt", "find", "-vx"]).is_err(), "letters after a `-` are flags");
        assert!(read(&["dt", "find", "--limit", "-1"]).is_err(), "and a value is not a pattern");
    }
}
