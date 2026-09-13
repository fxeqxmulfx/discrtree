//! `dt` — find a Lean declaration by shape, and lift it into a proof.

use clap::Parser;
use discrtree::interface::cli::Cli;
use discrtree::interface::run;

fn main() {
    if let Err(e) = run::run(Cli::parse()) {
        eprintln!("dt: {e}");
        std::process::exit(1);
    }
}
