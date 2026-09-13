//! Argument parsing only.

use clap::{Args, Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    name = "dt",
    version,
    about = "Find a Lean declaration by shape, and lift it into a proof",
    long_about = "discrtree indexes Lean corpora and answers two questions the \
                  repository answers badly: where is the declaration with this \
                  shape, and what does it take to use it here.\n\n\
                  Compiled sources are elaborated: shape search and exact \
                  dependencies work. Text sources are not, and every row from \
                  one is marked [text]."
)]
pub struct Cli {
    /// Path to discrtree.toml. Found by searching upwards when omitted.
    #[arg(long, global = true, value_name = "FILE")]
    pub config: Option<PathBuf>,

    /// Report what is being done, on stderr.
    #[arg(short, long, global = true)]
    pub verbose: bool,

    #[command(subcommand)]
    pub command: Command,
}

#[derive(Subcommand, Debug)]
pub enum Command {
    /// Write a starter discrtree.toml.
    Init {
        /// Overwrite an existing file.
        #[arg(long)]
        force: bool,
    },

    /// Dump a compiled source from the Lean environment into JSONL.
    Dump {
        /// Source name. All compiled sources when omitted.
        source: Option<String>,
        /// Skip proof terms: a much faster dump, with no dependency lists.
        #[arg(long)]
        no_deps: bool,
    },

    /// Read a text source with the scanner. Nothing here runs Lean.
    Scan {
        /// Source name. All text sources when omitted.
        source: Option<String>,
    },

    /// Clone or update a text source.
    Fetch {
        /// Source name. All git sources when omitted.
        source: Option<String>,
    },

    /// Build the search index from whatever has been dumped and scanned.
    Index {
        /// Rebuild from scratch instead of replacing source by source.
        #[arg(long)]
        rebuild: bool,
    },

    /// What is indexed, and whether it is elaborated.
    Status,

    /// Print a declaration and the import line that provides it.
    ///
    /// Several names at once cost one invocation instead of one each, which is
    /// the expensive part when this is driven by a program.
    Show {
        #[arg(required = true, value_name = "NAME")]
        names: Vec<String>,
        /// Print only the import lines, deduplicated.
        #[arg(long)]
        import_only: bool,
    },

    /// What a proof rests on.
    Deps {
        name: String,
        /// Levels to print. `all` gives the size of the closure instead.
        #[arg(long, default_value = "1")]
        depth: String,
    },

    /// Materialize a declaration and its tree into the project.
    Add {
        name: String,
        /// Actually write. Without it this is a dry run, which is the default
        /// because the depth of the tree cannot be predicted from the name.
        #[arg(long)]
        write: bool,
        /// Replace files that already exist.
        #[arg(long)]
        force: bool,
    },

    /// Search.
    Find(FindArgs),

    /// Look for declarations in a file that upstream already has.
    Dup {
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

    /// Substring of the declaration name.
    #[arg(long)]
    pub name: Option<String>,

    /// Head symbol of the conclusion, e.g. LE.le.
    #[arg(long)]
    pub concl: Option<String>,

    /// Constants the type must mention. Comma-separated, combined with AND.
    #[arg(long, value_delimiter = ',')]
    pub uses: Vec<String>,

    /// Module prefix, e.g. Mathlib.Analysis.
    #[arg(long = "in", value_name = "MODULE")]
    pub module: Option<String>,

    /// Restrict to one source.
    #[arg(long)]
    pub source: Option<String>,

    /// Restrict to one kind: theorem, def, structure, ...
    #[arg(long)]
    pub kind: Option<String>,

    /// Free text over type and docstring.
    #[arg(long)]
    pub text: Option<String>,

    /// Only rows that came out of the elaborator.
    #[arg(long)]
    pub elaborated: bool,

    /// Drop declarations proved by sorry.
    #[arg(long)]
    pub no_sorry: bool,

    /// Maximum results.
    #[arg(long, default_value_t = crate::domain::query::DEFAULT_LIMIT)]
    pub limit: usize,

    /// Print the full type of every hit.
    #[arg(long)]
    pub long: bool,
}
